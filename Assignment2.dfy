// -----------------------------------------------------
// Task 1: Method to compute the absolute value of an int
// -----------------------------------------------------

method Abs(x: int) returns (x': int)
  // Postconditions:
  ensures x' >= 0                        // Absolute value is always non-negative
  ensures x' == x            // Output must be either x or -x
{
  if x < 0 {
    x' := -x;                            // If negative, flip the sign
  } else {
    x' := x;                             // If non-negative, return as is
  }
}
