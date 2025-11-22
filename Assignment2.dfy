// -----------------------------------------------------
// Task 1: Method to compute the absolute value of an int
// -----------------------------------------------------

method Abs(x: int) returns (x': int)
  // Postconditions:
  ensures x' >= 0                        // Absolute value is always non-negative
  ensures x' == x || x' == -x            // Output must be either x or -x
{
  if x < 0 {
    x' := -x;                            // If negative, flip the sign
  } else {
    x' := x;                             // If non-negative, return as is
  }
}

// -----------------------------------------------------
// Task 2: Find First Negative in an Array
// -----------------------------------------------------

method FindFirstNegative(a: array?<int>) returns (index: int)
  requires a != null
  ensures index == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] >= 0
  ensures index != -1 ==> 
            0 <= index < a.Length &&
            a[index] < 0 &&
            (forall j :: 0 <= j < index ==> a[j] >= 0)
{
  var i := 0;

  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] >= 0
    decreases a.Length - i
  {
    if a[i] < 0 {
      index := i;
      return;
    }
    i := i + 1;
  }

  index := -1;
}

// -----------------------------------------------------
// Task 3: Factorial of n (Iterative)
// -----------------------------------------------------

function factorial(n: nat): nat
{
    if n == 0 then 1 else n * factorial(n - 1)
}

method Factorial(n: int) returns (result: int)
  requires n >= 0
  ensures result == factorial(n as nat)
{
  var i := 1;
  result := 1;

  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == factorial((i - 1) as nat)
    decreases n + 1 - i
  {
    result := result * i;
    i := i + 1;
  }
}

// -----------------------------------------------------
// Task 4: Tribonacci Sequence
// -----------------------------------------------------

function Trib(n: nat): nat
{
    if n == 0 then 0
    else if n == 1 then 1
    else if n == 2 then 1
    else Trib(n - 1) + Trib(n - 2) + Trib(n - 3)
}

method Tribonacci(n: int) returns (result: int)
  requires n >= 0
  ensures result == Trib(n as nat)
{
  if n == 0 {
    result := 0;
    return;
  }
  if n == 1 {
    result := 1;
    return;
  }
  if n == 2 {
    result := 1;
    return;
  }

  var t0 := 0;
  var t1 := 1;
  var t2 := 1;

  var i := 3;

  while i <= n
    invariant 3 <= i <= n + 1
    invariant t0 == Trib((i - 3) as nat)
    invariant t1 == Trib((i - 2) as nat)
    invariant t2 == Trib((i - 1) as nat)
    decreases n + 1 - i
  {
    var next := t0 + t1 + t2;
    t0 := t1;
    t1 := t2;
    t2 := next;
    i := i + 1;
  }

  result := t2;
}
