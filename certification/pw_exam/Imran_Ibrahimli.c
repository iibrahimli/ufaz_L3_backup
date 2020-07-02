/*@
    ensures \result >= a && \result >= b && \result >= c && (\result == a || \result == b || \result == c);
*/
int max3(int a, int b, int c) {
    if(a >= b && a >= c) return a;
    else if(b >= a && b >= c) return b;
    else return c;
}


/*@
    requires 0 < size < 1000;
    requires \valid(t+(0..size-1));

    assigns t[0..size-1];

    ensures \forall integer i; 0 <= i < size ==> t[i] == i*2;
*/
void double_arr(int t[], int size) {
    /*@
        loop invariant 0 <= i <= size;
        loop invariant \forall integer j; 0 <= j < i ==> t[j] == 2*j;
        loop variant size - i;
    */
    for(int i=0; i<size; ++i) {
        // i*2 might overflow, that is why I limit the size to 1000
        t[i] = i*2;
    }
}


/*@
    requires size > 1;
    requires \valid(t+(0..size-1));

    assigns \nothing;

    behavior non_decreasing:
        assumes \forall integer i, j; 0 <= i < j < size ==> t[i] <= t[j];
        ensures \result == 1;
    behavior decreasing:
        assumes \exists integer i, j; 0 <= i < j < size && t[i] > t[j];
        ensures \result == 0;
*/
int increasing(int t[], int size) {
    /*@
        loop invariant 0 <= i <= size-1;
        loop invariant \forall integer j; 0 <= j < i-1 ==> t[j] <= t[j+1];
        loop variant size - 1 - i;
    */
    for(int i=0; i<size-1; ++i) {
        if(t[i] > t[i+1]) {
            return 0;
        }
    }
    return 1;
}


/*@
    requires size > 1;
    requires \valid(t+(0..size-1));

    behavior non_decreasing:
        assumes \forall integer i, j; 0 <= i < j < size ==> t[i] <= t[j];
        ensures \result == 1;
    behavior non_increasing:
        assumes \forall integer i, j; 0 <= i < j < size ==> t[i] >= t[j];
        ensures \result == 1;
    behavior non_monotonic:
        assumes \exists integer i, j; 0 <= i < j < size-1 && ((t[i] <= t[i+1] && t[j] > t[j+1]) || (t[i] < t[i+1] && t[j] >= t[j+1]));
        ensures \result == 0;
*/
int monotonic(int t[], int size) {
    int non_dec = 1;
    int non_inc = 1;

    /*@
        loop invariant 0 <= i <= size - 1;
        loop invariant \forall integer j; 0 <= j < i-1 ==> t[j] <= t[j+1];
        loop variant size - i;
    */
    for(int i=0; i<size-1; ++i){
        // check if non-decreasing
        if(t[i] > t[i+1]) {
            non_dec = 0;
        }
    }

    /*@
        loop invariant 0 <= i <= size - 1;
        loop invariant \forall integer j; 0 <= j < i-1 ==> t[j] >= t[j+1];
        loop variant size - i;
    */
    for(int i=0; i<size-1; ++i){
        // check if non-increasing
        if(t[i] < t[i+1]) {
            non_inc = 0;
        }
    }

    return non_dec | non_inc;
}