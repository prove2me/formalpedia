-- Prove2me | Theorems.Thm_ErlerGross_digamma_multiplication_formula
-- name    : ErlerGross.digamma_multiplication_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T16:28:32.638422+00:00
-- url     : https://prove2.me/theorems/fe5ae410-9ebd-475d-9901-b4336ab7a551
-- title:
--   Gauss multiplication formula for the digamma function
-- statement:
--   For every positive integer n and every complex number z with positive real part, the sum of the digamma function at z, z + 1/n, ..., z + (n-1)/n equals n times its value at nz minus n log n. This is the digamma form of Gauss multiplication for the Gamma function.
-- source:
--   NIST DLMF, equation 5.5.6 (Gauss multiplication formula), https://dlmf.nist.gov/5.5.E6

import Mathlib

namespace ErlerGross

theorem digamma_multiplication_formula (n : Nat) (hn : 0 < n) (z : Complex) (hz : 0 < z.re) :
    Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
      n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex) := by
  sorry

end ErlerGross
