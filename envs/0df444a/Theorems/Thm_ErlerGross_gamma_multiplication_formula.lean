-- Prove2me | Theorems.Thm_ErlerGross_gamma_multiplication_formula
-- name    : ErlerGross.gamma_multiplication_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T18:28:13.883189+00:00
-- url     : https://prove2.me/theorems/625fc10a-f4d7-475f-9256-1d7e52b63a28
-- title:
--   Gauss multiplication formula for Gamma, exponential form
-- statement:
--   For every positive integer n, the product of Gamma(z + k/n) over k = 0,...,n-1 is a nonzero constant (depending on n) times exp(-n z log n) Gamma(nz). This is Gauss multiplication formula, with the z-independent factor left unspecified.
-- source:
--   NIST Digital Library of Mathematical Functions, section 5.5(iii), equation 5.5.6: https://dlmf.nist.gov/5.5.E6

import Mathlib

namespace ErlerGross
theorem gamma_multiplication_formula (n : Nat) (hn : 0 < n) :
    Exists fun c : Complex => And (Not (c = 0)) (forall z : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * z * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * z)) := by
  sorry
end ErlerGross
