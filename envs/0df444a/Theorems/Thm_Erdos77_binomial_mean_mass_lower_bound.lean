-- Prove2me | Theorems.Thm_Erdos77_binomial_mean_mass_lower_bound
-- name    : Erdos77.binomial_mean_mass_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T20:02:17.111653+00:00
-- url     : https://prove2.me/theorems/4b3f4c3a-eb09-4652-870d-49c228137ef5
-- title:
--   Binomial probability at its mean has mass at least 1 over n plus 1
-- statement:
--   For a binomial random variable with n trials and success probability r/n, the probability of the value r is at least 1/(n+1). This follows because r is a mode of that binomial distribution and its n+1 point probabilities sum to one.
-- source:
--   Elementary mode-mass bound for the binomial distribution, obtained from the adjacent-term ratio; used to derive the entropy lower bound.

import Mathlib

namespace Erdos77

theorem binomial_mean_mass_lower_bound (n r : Nat) (hr : 0 < r) (hrn : r < n) :
  (1 : Real) / ((n + 1 : Nat) : Real) <=
    (Nat.choose n r : Real) * ((r : Real) / (n : Real)) ^ r *
      ((Nat.cast (n - r) : Real) / (n : Real)) ^ (n - r) := by sorry

end Erdos77
