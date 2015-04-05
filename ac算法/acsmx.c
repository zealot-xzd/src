/*
**
** $Id$
**
** Multi-Pattern Search Engine
**
** Aho-Corasick State Machine -  uses a Deterministic Finite Automata - DFA
**
** Copyright (C) 2014 Cisco and/or its affiliates. All rights reserved.
** Copyright (C) 2002-2013 Sourcefire, Inc.
** Marc Norton
**
**
** This program is free software; you can redistribute it and/or modify
** it under the terms of the GNU General Public License Version 2 as
** published by the Free Software Foundation.  You may not use, modify or
** distribute this program under any other version of the GNU General
** Public License.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program; if not, write to the Free Software
** Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
**
**
**   Reference - Efficient String matching: An Aid to Bibliographic Search
**               Alfred V Aho and Margaret J Corasick
**               Bell Labratories
**               Copyright(C) 1975 Association for Computing Machinery,Inc
**
**   Implemented from the 4 algorithms in the paper by Aho & Corasick
**   and some implementation ideas from 'Practical Algorithms in C'
**
**   Notes:
**     1) This version uses about 1024 bytes per pattern character - heavy  on the memory.
**     2) This algorithm finds all occurrences of all patterns within a
**        body of text.
**     3) Support is included to handle upper and lower case matching.
**     4) Some comopilers optimize the search routine well, others don't, this makes all the difference.
**     5) Aho inspects all bytes of the search text, but only once so it's very efficient,
**        if the patterns are all large than the Modified Wu-Manbar method is often faster.
**     6) I don't subscribe to any one method is best for all searching needs,
**        the data decides which method is best,
**        and we don't know until after the search method has been tested on the specific data sets.
**
**
**  May 2002  : Marc Norton 1st Version
**  June 2002 : Modified interface for SNORT, added case support
**  Aug 2002  : Cleaned up comments, and removed dead code.
**  Nov 2,2002: Fixed queue_init() , added count=0
**
**
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <ctype.h>
#include <errno.h>
#include<unistd.h>

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "acsmx.h"

#ifdef DYNAMIC_PREPROC_CONTEXT
#include "sf_dynamic_preprocessor.h"
#endif //DYNAMIC_PREPROC_CONTEXT

#define MEMASSERT(p,s) if(!p){fprintf(stderr,"ACSM-No Memory: %s!\n",s);exit(0);}

long long max_memory = 0;
long long cpy_mem = 0;

/*static void Print_DFA( ACSM_STRUCT * acsm );*/

/*
*
*/
static void *
AC_MALLOC (int n)
{
  void *p;
  p = calloc (1,n);
  if (p)
    max_memory += n;
  return p;
}


/*
*
*/
static void
AC_FREE (void *p)
{
  if (p)
    free (p);
}


/*
*    Simple QUEUE NODE
*/
typedef struct _qnode
{
  int state;
   struct _qnode *next;
}
QNODE;

/*
*    Simple QUEUE Structure
*/
typedef struct _queue
{
  QNODE * head, *tail;
  int count;
}
QUEUE;

/*
*
*/
static void
queue_init (QUEUE * s)
{
  s->head = s->tail = 0;
  s->count = 0;
}


/*
*  Add Tail Item to queue
*/
static void
queue_add (QUEUE * s, int state)
{
  QNODE * q;
  if (!s->head)
    {
      q = s->tail = s->head = (QNODE *) AC_MALLOC (sizeof (QNODE));
      MEMASSERT (q, "queue_add");
      q->state = state;
      q->next = 0;
    }
  else
    {
      q = (QNODE *) AC_MALLOC (sizeof (QNODE));
      MEMASSERT (q, "queue_add");
      q->state = state;
      q->next = 0;
      s->tail->next = q;
      s->tail = q;
    }
  s->count++;
}


/*
*  Remove Head Item from queue
*/
static int
queue_remove (QUEUE * s)
{
  int state = 0;
  QNODE * q;
  if (s->head)
    {
      q = s->head;
      state = q->state;
      s->head = s->head->next;
      s->count--;
      if (!s->head)
      {
          s->tail = 0;
          s->count = 0;
      }
      AC_FREE (q);
    }
  return state;
}


/*
*
*/
static int
queue_count (QUEUE * s)
{
  return s->count;
}


/*
*
*/
static void
queue_free (QUEUE * s)
{
  while (queue_count (s))
    {
      queue_remove (s);
    }
}


/*
** Case Translation Table
*/
static unsigned char xlatcase[256];

/*
*
*/
  static void
init_xlatcase ()
{
  int i;
  for (i = 0; i < 256; i++)
    {
      xlatcase[i] = (unsigned char)toupper (i);
    }
}


/*
*
*/
static inline void
ConvertCaseEx (unsigned char *d, unsigned char *s, int m)
{
  int i;
  for (i = 0; i < m; i++)
    {
      d[i] = xlatcase[s[i]];
    }
}


/*
*
*/
static ACSM_PATTERN *
CopyMatchListEntry (ACSM_PATTERN * px)
{
  ACSM_PATTERN * p;
  p = (ACSM_PATTERN *) AC_MALLOC (sizeof (ACSM_PATTERN));
  cpy_mem += sizeof (ACSM_PATTERN);
  MEMASSERT (p, "CopyMatchListEntry");
  memcpy (p, px, sizeof (ACSM_PATTERN));
  px->udata->ref_count++;
  p->next = 0;
  return p;
}


/*
*  Add a pattern to the list of patterns terminated at this state.
*  Insert at front of list.
*/
static void
AddMatchListEntry (ACSM_STRUCT * acsm, int state, ACSM_PATTERN * px)
{
  ACSM_PATTERN * p;
  p = (ACSM_PATTERN *) AC_MALLOC (sizeof (ACSM_PATTERN));
  MEMASSERT (p, "AddMatchListEntry");
  memcpy (p, px, sizeof (ACSM_PATTERN));
  p->next = acsm->acsmStateTable[state].MatchList;
  acsm->acsmStateTable[state].MatchList = p;
}


/*
   Add Pattern States
*/
static void
AddPatternStates (ACSM_STRUCT * acsm, ACSM_PATTERN * p)
{
  unsigned char *pattern;
  int state=0, next, n;
  n = p->n;
  pattern = p->casepatrn;
  //pattern = p->patrn;

    /*
     *  Match up pattern with existing states
     */
    for (; n > 0; pattern++, n--)
    {
      next = acsm->acsmStateTable[state].NextState[*pattern];
      if (next == ACSM_FAIL_STATE)
        break;
      state = next;
    }

    /*
     *   Add new states for the rest of the pattern bytes, 1 state per byte
     */
    for (; n > 0; pattern++, n--)
    {
      acsm->acsmNumStates++;
      acsm->acsmStateTable[state].NextState[*pattern] = acsm->acsmNumStates;
      state = acsm->acsmNumStates;
    }

  AddMatchListEntry (acsm, state, p);
}


/*
*   Build Non-Deterministic Finite Automata
*/
static void
Build_NFA (ACSM_STRUCT * acsm)
{
  int r, s;
  int i;
  QUEUE q, *queue = &q;
  ACSM_PATTERN * mlist=0;
  ACSM_PATTERN * px=0;

    /* Init a Queue */
    queue_init (queue);

    /* Add the state 0 transitions 1st */
    for (i = 0; i < ALPHABET_SIZE; i++)
    {
      s = acsm->acsmStateTable[0].NextState[i];
      if (s)
      {
        queue_add (queue, s);
        acsm->acsmStateTable[s].FailState = 0;
      }
    }

    /* Build the fail state transitions for each valid state */
    while (queue_count (queue) > 0)
    {
      r = queue_remove (queue);

      /* Find Final States for any Failure */
      for (i = 0; i < ALPHABET_SIZE; i++)
      {
        int fs, next;
        if ((s = acsm->acsmStateTable[r].NextState[i]) != ACSM_FAIL_STATE)
        {
          queue_add (queue, s);
          fs = acsm->acsmStateTable[r].FailState;

          /*
           *  Locate the next valid state for 'i' starting at s
           */
          while ((next=acsm->acsmStateTable[fs].NextState[i]) ==
                 ACSM_FAIL_STATE)
          {
            fs = acsm->acsmStateTable[fs].FailState;
          }

          /*
           *  Update 's' state failure state to point to the next valid state
           */
          acsm->acsmStateTable[s].FailState = next;

          /*
           *  Copy 'next'states MatchList to 's' states MatchList,
           *  we copy them so each list can be AC_FREE'd later,
           *  else we could just manipulate pointers to fake the copy.
           */
          for (mlist  = acsm->acsmStateTable[next].MatchList;
               mlist != NULL ;
               mlist  = mlist->next)
          {
              px = CopyMatchListEntry (mlist);

              if( !px )
              {
                printf("*** Out of memory Initializing Aho Corasick in acsmx.c ****\n");
              }

              /* Insert at front of MatchList */
              px->next = acsm->acsmStateTable[s].MatchList;
              acsm->acsmStateTable[s].MatchList = px;
          }
        }
      }
    }
    /* Clean up the queue */
    queue_free (queue);
}


/*
*   Build Deterministic Finite Automata from NFA
*/
static void
Convert_NFA_To_DFA (ACSM_STRUCT * acsm)
{
  int r, s;
  int i;
  QUEUE q, *queue = &q;

    /* Init a Queue */
    queue_init (queue);

    /* Add the state 0 transitions 1st */
    for (i = 0; i < ALPHABET_SIZE; i++)
    {
      s = acsm->acsmStateTable[0].NextState[i];
      if (s)
      {
        queue_add (queue, s);
      }
    }

    /* Start building the next layer of transitions */
    while (queue_count (queue) > 0)
    {
      r = queue_remove (queue);

      /* State is a branch state */
      for (i = 0; i < ALPHABET_SIZE; i++)
      {
        if ((s = acsm->acsmStateTable[r].NextState[i]) != ACSM_FAIL_STATE)
        {
            queue_add (queue, s);
        }
        else
        {
            acsm->acsmStateTable[r].NextState[i] =
            acsm->acsmStateTable[acsm->acsmStateTable[r].FailState].
            NextState[i];
        }
      }
    }

    /* Clean up the queue */
    queue_free (queue);
}


/*
*
*/
ACSM_STRUCT * acsmNew (void (*userfree)(void *p),
                       void (*optiontreefree)(void **p),
                       void (*neg_list_free)(void **p))
{
  ACSM_STRUCT * p;
  init_xlatcase ();
  p = (ACSM_STRUCT *) AC_MALLOC (sizeof (ACSM_STRUCT));
  MEMASSERT (p, "acsmNew");
  if (p)
  {
    memset (p, 0, sizeof (ACSM_STRUCT));
    p->userfree              = userfree;
    p->optiontreefree        = optiontreefree;
    p->neg_list_free         = neg_list_free;
  }
  return p;
}


/*
*   Add a pattern to the list of patterns for this state machine
*/
int
acsmAddPattern (ACSM_STRUCT * p, unsigned char *pat, int n, int nocase,
            int offset, int depth, int negative, void * id, int iid)
{
  ACSM_PATTERN * plist;
  plist = (ACSM_PATTERN *) AC_MALLOC (sizeof (ACSM_PATTERN));
  MEMASSERT (plist, "acsmAddPattern");
  plist->patrn = (unsigned char *) AC_MALLOC (n);
  ConvertCaseEx (plist->patrn, pat, n);
  plist->casepatrn = (unsigned char *) AC_MALLOC (n);
  memcpy (plist->casepatrn, pat, n);

  plist->udata = (ACSM_USERDATA *)AC_MALLOC(sizeof(ACSM_USERDATA));
  MEMASSERT (plist->udata, "acsmAddPattern");
  plist->udata->ref_count = 1;
  int len = strlen((const char*)id);
  plist->udata->id= (unsigned char *) AC_MALLOC (len + 1);
  memcpy (plist->udata->id, id, len);

  plist->n = n;
  plist->nocase = nocase;
  plist->negative = negative;
  plist->offset = offset;
  plist->depth = depth;
  plist->iid = iid;
  plist->next = p->acsmPatterns;
  p->acsmPatterns = plist;
  p->numPatterns++;
  return 0;
}

static int acsmBuildMatchStateTrees( ACSM_STRUCT * acsm,
                                     int (*build_tree)(void * id, void **existing_tree),
                                     int (*neg_list_func)(void *id, void **list) )
{
    int i, cnt = 0;
    ACSM_PATTERN * mlist;

    /* Find the states that have a MatchList */
    for (i = 0; i < acsm->acsmMaxStates; i++)
    {
        for ( mlist=acsm->acsmStateTable[i].MatchList;
              mlist!=NULL;
              mlist=mlist->next )
        {
            if (mlist->udata->id)
            {
                if (mlist->negative)
                {
                    neg_list_func(mlist->udata->id, &acsm->acsmStateTable[i].MatchList->neg_list);
                }
                else
                {
                    build_tree(mlist->udata->id, &acsm->acsmStateTable[i].MatchList->rule_option_tree);
                }
            }

            cnt++;
        }

        if (acsm->acsmStateTable[i].MatchList)
        {
            /* Last call to finalize the tree */
            build_tree(NULL, &acsm->acsmStateTable[i].MatchList->rule_option_tree);
        }
    }

    return cnt;
}

static int acsmBuildMatchStateTreesWithSnortConf( struct _SnortConfig *sc, ACSM_STRUCT * acsm,
                                                  int (*build_tree)(struct _SnortConfig *, void * id, void **existing_tree),
                                                  int (*neg_list_func)(void *id, void **list) )
{
    int i, cnt = 0;
    ACSM_PATTERN * mlist;

    /* Find the states that have a MatchList */
    for (i = 0; i < acsm->acsmMaxStates; i++)
    {
        for ( mlist=acsm->acsmStateTable[i].MatchList;
              mlist!=NULL;
              mlist=mlist->next )
        {
            if (mlist->udata->id)
            {
                if (mlist->negative)
                {
                    neg_list_func(mlist->udata->id, &acsm->acsmStateTable[i].MatchList->neg_list);
                }
                else
                {
                    build_tree(sc, mlist->udata->id, &acsm->acsmStateTable[i].MatchList->rule_option_tree);
                }
            }

            cnt++;
        }

        if (acsm->acsmStateTable[i].MatchList)
        {
            /* Last call to finalize the tree */
            build_tree(sc, NULL, &acsm->acsmStateTable[i].MatchList->rule_option_tree);
        }
    }

    return cnt;
}


/*
*   Compile State Machine
*/
static inline int
_acsmCompile (ACSM_STRUCT * acsm)
{
    int i, k;
    ACSM_PATTERN * plist;

    /* Count number of states */
    acsm->acsmMaxStates = 1;
    for (plist = acsm->acsmPatterns; plist != NULL; plist = plist->next)
    {
        acsm->acsmMaxStates += plist->n;
    }
    acsm->acsmStateTable =
        (ACSM_STATETABLE *) AC_MALLOC (sizeof (ACSM_STATETABLE) *
                                        acsm->acsmMaxStates);
	printf("sateTable's mem: %d\n", sizeof (ACSM_STATETABLE) * acsm->acsmMaxStates);
    MEMASSERT (acsm->acsmStateTable, "acsmCompile");
    memset (acsm->acsmStateTable, 0,
        sizeof (ACSM_STATETABLE) * acsm->acsmMaxStates);

    /* Initialize state zero as a branch */
    acsm->acsmNumStates = 0;

    /* Initialize all States NextStates to FAILED */
    for (k = 0; k < acsm->acsmMaxStates; k++)
    {
        for (i = 0; i < ALPHABET_SIZE; i++)
        {
            acsm->acsmStateTable[k].NextState[i] = ACSM_FAIL_STATE;
        }
    }

    /* Add each Pattern to the State Table */
    for (plist = acsm->acsmPatterns; plist != NULL; plist = plist->next)
    {
        AddPatternStates (acsm, plist);
    }

    /* Set all failed state transitions to return to the 0'th state */
    for (i = 0; i < ALPHABET_SIZE; i++)
    {
        if (acsm->acsmStateTable[0].NextState[i] == ACSM_FAIL_STATE)
        {
            acsm->acsmStateTable[0].NextState[i] = 0;
        }
    }

    /* Build the NFA  */
    Build_NFA (acsm);

    /* Convert the NFA to a DFA */
    Convert_NFA_To_DFA (acsm);

      printf ("ACSMX-Max Memory: %lld bytes, ACSMX-Max states: %d\n", max_memory,
        acsm->acsmMaxStates);

    //Print_DFA( acsm );
	printf("cpy_mem:%lld\n",cpy_mem);

    return 0;
}

int
acsmCompile (ACSM_STRUCT * acsm,
             int (*build_tree)(void * id, void **existing_tree),
             int (*neg_list_func)(void *id, void **list))
{
    int rval;

    if ((rval = _acsmCompile (acsm)))
        return rval;

    if (build_tree && neg_list_func)
    {
        acsmBuildMatchStateTrees(acsm, build_tree, neg_list_func);
    }

    return 0;
}

int
acsmCompileWithSnortConf (struct _SnortConfig *sc, ACSM_STRUCT * acsm,
                          int (*build_tree)(struct _SnortConfig *, void * id, void **existing_tree),
                          int (*neg_list_func)(void *id, void **list))
{
    int rval;

    if ((rval = _acsmCompile (acsm)))
        return rval;

    if (build_tree && neg_list_func)
    {
        acsmBuildMatchStateTreesWithSnortConf(sc, acsm, build_tree, neg_list_func);
    }

    return 0;
}

static unsigned char Tc[1024*1024]; //1M

/*
*   Search Text or Binary Data for Pattern matches
*/
int
acsmSearch (ACSM_STRUCT * acsm, unsigned char *Tx, int n,
            int (*Match)(void * id, void *tree, int index, void *data, void *neg_list),
            void *data, int* current_state )
{
    int state = 0;
    ACSM_PATTERN * mlist,*temp;
    unsigned char *Tend;
    ACSM_STATETABLE * StateTable = acsm->acsmStateTable;
    int nfound = 0;
    unsigned char *T;
    int index;
    char pattern[512]={0};
    int len=0;
    /* Case conversion */
    //ConvertCaseEx (Tc, Tx, n);
    T = Tx;
    //T = Tc;
    Tend = T + n;

    if ( !current_state )
    {
        return 0;
    }

    state = *current_state;

    for (; T < Tend; T++)
    {
        state = StateTable[state].NextState[*T];

        if( StateTable[state].MatchList != NULL )
        {
           for(mlist = StateTable[state].MatchList; mlist != NULL; mlist = mlist->next)
           {
               index = T - mlist->n + 1 - Tx;
               //index = T - mlist->n + 1 - Tc;
               nfound++;
               len = sprintf(pattern, "(id)%s: (pos)%d: (key)",mlist->udata->id,index);
		memcpy(pattern+len,mlist->casepatrn,mlist->n);
	//	memcpy(pattern+len,mlist->patrn,mlist->n);
               //fprintf(stdout, "pattern-id:%d || pattern:%s || position:%d\n",mlist->iid,mlist->patrn,index);
	       printf("%s\n",pattern);
	       memset(pattern, 0, sizeof(pattern));
           }
	       printf("==================\n");
        }
    }
    return nfound;
}


/*
*   Free all memory
*/
void
acsmFree (ACSM_STRUCT * acsm)
{
    int i;
    ACSM_PATTERN * mlist, *ilist;
    for (i = 0; i < acsm->acsmMaxStates; i++)
    {
        mlist = acsm->acsmStateTable[i].MatchList;
        while (mlist)
        {
            ilist = mlist;
            mlist = mlist->next;

            ilist->udata->ref_count--;
            if (ilist->udata->ref_count == 0)
            {
                if (acsm->userfree && ilist->udata->id)
                    acsm->userfree(ilist->udata->id);

                AC_FREE(ilist->udata);
            }

            if (ilist->rule_option_tree && acsm->optiontreefree)
            {
                acsm->optiontreefree(&(ilist->rule_option_tree));
            }

            if (ilist->neg_list && acsm->neg_list_free)
            {
                acsm->neg_list_free(&(ilist->neg_list));
            }

            AC_FREE (ilist);
        }
    }
    AC_FREE (acsm->acsmStateTable);
    mlist = acsm->acsmPatterns;
    while(mlist)
    {
        ilist = mlist;
        mlist = mlist->next;
        AC_FREE(ilist->patrn);
        AC_FREE(ilist->casepatrn);
        AC_FREE(ilist);
    }
    AC_FREE (acsm);
}

int acsmPatternCount ( ACSM_STRUCT * acsm )
{
    return acsm->numPatterns;
}

int acsmStateCount ( ACSM_STRUCT * acsm )
{
    return acsm->acsmNumStates;
}



/*
 *
 */
/*
static void Print_DFA( ACSM_STRUCT * acsm )
{
    int k;
    int i;
    int next;

    for (k = 0; k < acsm->acsmMaxStates; k++)
    {
      for (i = 0; i < ALPHABET_SIZE; i++)
    {
      next = acsm->acsmStateTable[k].NextState[i];

      if( next == 0 || next ==  ACSM_FAIL_STATE )
      {
           if( isprint(i) )
             printf("%3c->%-5d\t",i,next);
           else
             printf("%3d->%-5d\t",i,next);
      }
    }
      printf("\n");
    }

}
*/


int acsmPrintDetailInfo(ACSM_STRUCT * p)
{
    if(p)
        p = p;
    return 0;
}

int acsmPrintSummaryInfo(ACSM_STRUCT *p)
{

    printf("+--[Pattern Matcher:Aho-Corasick Summary]----------------------\n");
    if( max_memory < 1024*1024 )
    printf("| Memory           : %.2fKbytes\n", (float)max_memory/1024 );
    else
    printf("| Memory           : %.2fMbytes\n", (float)max_memory/(1024*1024) );
    printf("+-------------------------------------------------------------\n");

    return 0;
}



/*
*  Text Data Buffer
*/
unsigned char text[102400];

/*
*    A Match is found
*/
  int
MatchFound (void * id, void *tree, int index, void *data, void *neg_list)
{
  fprintf (stdout, "%s\n", (char *) id);
  fprintf (stdout, "%d\n", index);
  return 0;
}



#define FILE_LINE_CHUNK 1024
int init_pattern(ACSM_STRUCT * acsm, char *filename)
{
    char buf[FILE_LINE_CHUNK] = { 0 };
    FILE *pF;
    int len;
    int id = 0;
    int i = 0;
    char *pSave,*pId,*pPattern;
    
    if(NULL == filename || 0 ==*filename)
        return -1;
    if(NULL == (pF = fopen(filename, "r"))){
        perror("open file faild!");
        return -1;
    }
    
    
    while(NULL != fgets(buf,FILE_LINE_CHUNK,pF))
    {
        id++;
	len = strlen(buf);
        if(len <= 1)
		continue;
        if(buf[len-1] != '\n')
	{
		printf("pattern %d been truncated!\n",id);	
		do
		{
			fgets(buf,FILE_LINE_CHUNK,pF);

		}while(!strchr(buf,'\n'));
		continue;
	} 
	if ('#' == buf[0])
        {
            continue;
        }

	buf[len-1] = '\0';
	if(buf[len-2] == '\r')
		buf[len-2] = '\0';

	pSave = NULL;
        pId  = strtok_r(buf, " \t\r\n", &pSave);
        if (!pId)
		continue;
        pPattern = strtok_r(NULL, " \t\r\n", &pSave);
        if (!pPattern)
		continue;
        acsmAddPattern (acsm, (unsigned char*)pPattern, strlen (pPattern), 0, 0, 0, 0, pId, id - 1);
    }
    return 0;
}
int get_file_contet(const char *file, char **content)
{
    char buff[2260];
    FILE *file_r = NULL;
    FILE *file_w = NULL;
    size_t size;
    size_t RetSize;
    if (file == NULL || 0 == *file
        || (0 != access (file, F_OK | R_OK)))
        return 0;
    
    file_r = fopen (file, "r");
    file_w = open_memstream (content, &size);
    if (file_r == NULL || file_w == NULL)
    {
        if (file_r != NULL)
            fclose (file_r);
        if (file_w != NULL)
            fclose (file_w);
        return 0;
    }
    for(;;){
        if(0 == (RetSize = fread(buff, 1, 2048, file_r)))
            if(feof(file_r))
                break;
            else if(ferror(file_r)){
                printf("read file %s error %s", file, strerror(errno));
                break;
            }
        fwrite(buff, sizeof(char), RetSize, file_w);
    }
    
    fclose (file_w);
    fclose (file_r);
    return size;
}

/*
*
*/
  int
main (int argc, char **argv)
{
  int i, nocase = 0;
  int state=0;
  ACSM_STRUCT * acsm;
  char *content;
  if (argc < 3)

    {
      fprintf (stderr,
        "Usage: acsmx text pattern-file\n");
      exit (0);
    }
	get_file_contet(argv[1], &content);
  acsm = acsmNew (AC_FREE,NULL,NULL);
  //strcpy (text, argv[1]);
  for(i=0; i<strlen(content); i++)
      text[i] = (unsigned char)content[i];
  for (i = 1; i < argc; i++)
    if (strcmp (argv[i], "-nocase") == 0)
      nocase = 1;

    init_pattern(acsm,argv[2]);
  
  acsmCompile (acsm,NULL,NULL);
  acsmSearch (acsm, text, strlen ((char*)text), MatchFound, (void *) 0, &state);
  acsmPrintSummaryInfo(acsm);
  printf("pattern num:%d\n",acsmPatternCount ( acsm ));
  printf("state num:%d\n",acsmStateCount( acsm ));
  free(content);
  acsmFree (acsm);
  printf ("normal pgm end\n");
  return (0);
}

