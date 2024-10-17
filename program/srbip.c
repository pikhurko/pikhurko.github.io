/* asymptotic computation of size Ramsey function for complete
   bipartite graphs; (C) 2000 Oleg Pikhurko;
   distributed under GNU General Public Licence: see http://www.gnu.org 

   This program computes 
   $m=\lim_{n\to\infty} \hat (K_{s_1,t_{1,n}},\dots, K_{s_q,t_{q,n}},
   K_{s_{q+1},t_{q+1}}, \dots,K_{s_r,t_r})/n$,
   where $t_{i,n}=t_in+o(n)$ with each $t_i$ being a fixed positive real.

   Input: 
   q r
   s[1] t[1]
   ...
   s[q] t[q]
   max(s[q+1],t[q+1])
   ...
   max(s[r],t[r])

   Output: the value of $m$.

   Compiling: the code has to be linked with lp_solve 3.2 which is
   freely available at ftp://ftp.ics.ele.tue.nl/pub/lp_solve/

   Description of the algorithm (and the proof of its correctness) can
   be found in the e-print "Asymptotic Size Ramsey Results for
   Bipartite Graphs" by Oleg Pikhurko at http://www.arXiv.org */


#include <stdio.h>
#include "lpkit.h"

#define MAXR 1000


/* computation of the binomial coefficient */
int binom(int, int);


int main(void)
{

  int q, r, sigma=0;
  float t[MAXR];
  int s[MAXR], a[MAXR];
  int i, j, l, first_lp=1;
  int current_column, ncolumns;
  lprec *lp;
  REAL best_bound;

  printf("Asymptotic computation of size Ramsey function for complete");
  printf(" bipartite graphs.\nSee the source code for details.\n");

  printf("Please enter q and r: ");

  scanf("%d %d", &q,&r);

  s[0]=0;

  for (i=1; i<=q; i++) {
    printf("Enter s[%d] and t[%d]: ", i,i);
    scanf("%d %f",&(s[i]),&(t[i]));
    sigma+=s[i]-1;
    t[0]+=t[i];
  }

  for (i=q+1; i<=r; i++) {
    printf("Enter max(s[%d],t[%d]): ", i,i);
    scanf("%d",&s[i]);
    sigma+=s[i]-1;
    s[0]+=s[i]-1; 
  }

  l=sigma+1;

  do {

    /* construct all partitions a[1]+...+a[r]=l-s[0] in lex order */
    /* ncolumns counts the number of partitions */
    ncolumns=binom(l-s[0]+q-1,q-1); 


    lp=make_lp(q,ncolumns); /* q contraints and ncolumns variables */
    for(j=1;j<=ncolumns;j++)
      set_mat(lp,0,j,(REAL) l); /* objective function is in row 0;
				   NOTE: it is already multiplied by l */
    set_maxim(lp); /* we want to maximize objective function */

    for(j=1;j<=q;j++) {/* set constraints */
      set_rh(lp, j, (REAL) t[j]*binom(l,s[j]) );
      set_constr_type(lp,j,LE);
    }

    /* the first partition */
    current_column=1;
    for(i=1;i<q;i++)
      a[i]=0;
    a[q]=l-s[0];

    do {

      /* add the current_column's coefficients */

      for(j=1;j<=q;j++)
	set_mat(lp, j, current_column, (REAL) binom(a[j],s[j]) );

      /* find next partition */

      i=q+1; /* find the largest i with a[i]>0 */
      while(a[--i]==0) ;
    
      if ( i>1 ) { /* there are more partitions */

	current_column++;
	a[i-1]++; a[q]=a[i]-1;
	if(i<q) a[i]=0; /* beware that i might be equal q */

      }     

    } while ( i>1 );

    if(current_column!=ncolumns) { /* something is wrong */
      printf("current_column=%d ncolumns=%d l=%d\n",
	     current_column,ncolumns,l);
      exit(1);
    }

    /* now we invoke an lp solver and get its output */
    if(solve(lp)) {
      printf("Could not solve LP!\n");
      print_lp(lp);
      exit(1);
    }

    if (first_lp) {
      best_bound= lp->best_solution[0];
      first_lp=0;
    } else
      if( best_bound >  lp->best_solution[0] )
	best_bound = lp->best_solution[0];


 /* printing various debugging information
    for(j=1;j<=q;j++)
      printf("s[j]=%d, t[j]=%f\n",s[j],t[j]);
    print_lp(lp);
    printf("l=%d, solution=",l);
    print_solution(lp);
    printf("Best bound so far %f\n",(float) best_bound);
    printf("t[0]=%f\n",t[0]);
 */

    delete_lp(lp);

    l++; 

  }
  while ( (l*t[0]) <= best_bound );


  printf("The value of\n $\\lim \\hat r(");
  for(j=1;j<=q;j++)
    printf("K_{%d,%.2fn},", s[j],(float) t[j]);
  for(j=q+1;j<=r;j++)
    printf("K_{%d,M},",s[j]);
  printf(")/n$\nis %f\n\n", (float) best_bound);

  return 0;

}



int binom(int n, int m)
{

  int i, en=1, den=1;

  if (n<0 || n<m)
    return 0;

  if (2*m>n)
    m=n-m;

  for(i=1;i<=m;i++) {
    en*=n-i+1;
    den*=i;
  }

  return en/den;

}



