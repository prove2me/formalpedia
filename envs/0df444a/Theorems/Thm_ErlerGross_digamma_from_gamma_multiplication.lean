-- Prove2me | Theorems.Thm_ErlerGross_digamma_from_gamma_multiplication
-- name    : ErlerGross.digamma_from_gamma_multiplication
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T18:28:13.287979+00:00
-- url     : https://prove2.me/theorems/95ba1abf-4d37-4ef7-bb85-81cf5d41528b
-- title:
--   Logarithmic derivative of the Gamma multiplication identity
-- statement:
--   Assuming the Gamma multiplication identity, logarithmic differentiation at a point in the right half-plane gives the corresponding multiplication formula for the digamma function.
-- source:
--   Derived by logarithmic differentiation of Gauss multiplication formula, NIST DLMF section 5.5(iii), equations 5.5.6 and 5.5.9: https://dlmf.nist.gov/5.5.E6

import Mathlib

namespace ErlerGross
theorem digamma_from_gamma_multiplication (n : Nat) (hn : 0 < n) (z : Complex)
    (hz : 0 < z.re) (c : Complex) (hc : Not (c = 0))
    (hmul : forall w : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (w + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * w * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * w)) :
    Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
      n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex) := by
  sorry
end ErlerGross
