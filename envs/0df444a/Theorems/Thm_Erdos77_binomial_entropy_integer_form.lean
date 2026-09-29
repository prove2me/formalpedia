-- Prove2me | Theorems.Thm_Erdos77_binomial_entropy_integer_form
-- name    : Erdos77.binomial_entropy_integer_form
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T19:58:25.720002+00:00
-- url     : https://prove2.me/theorems/6592d236-ce78-4587-b86d-64e1b8b2f555
-- title:
--   Multiplicative binomial entropy bound
-- statement:
--   For integers 0 < r < n, the binomial coefficient multiplied by r^r and (n-r)^(n-r), and by the number n+1 of terms, is at least n^n. This is the multiplicative form of the entropy lower bound.
-- source:
--   Standard binomial mode-mass lower bound.

import Mathlib

namespace Erdos77
theorem binomial_entropy_integer_form (n r : Nat) (hr : 0 < r) (hrn : r < n) :
    (n : Real) ^ n <= ((n + 1 : Nat) : Real) * (Nat.choose n r : Real) *
      (r : Real) ^ r * (Nat.cast (n - r) : Real) ^ (n - r) := by sorry
end Erdos77
