-- Prove2me | Theorems.Thm_ErlerGross_gamma_multiplication_formula_of_digamma
-- name    : ErlerGross.gamma_multiplication_formula_of_digamma
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T19:49:43.627976+00:00
-- url     : https://prove2.me/theorems/a1e7fbe3-3035-4e05-9a01-7a8cac646f6f
-- title:
--   Derive Gauss multiplication from the digamma multiplication identity
-- statement:
--   For each positive integer n, if the digamma multiplication identity holds at every complex z with positive real part, then there is a nonzero constant c such that the Gauss multiplication identity for Gamma holds for every complex z.
-- source:
--   Reduction lemma for Gauss multiplication formula; compare NIST DLMF 5.5.6 and 5.5.9, https://dlmf.nist.gov/5.5.E6 and https://dlmf.nist.gov/5.5.E9

import Mathlib

namespace ErlerGross
theorem gamma_multiplication_formula_of_digamma (n : Nat) (hn : 0 < n)
    (hpsi : forall z : Complex, 0 < z.re ->
      Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
        n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex)) :
    Exists fun c : Complex => And (Not (c = 0)) (forall z : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) := by
  sorry
end ErlerGross
