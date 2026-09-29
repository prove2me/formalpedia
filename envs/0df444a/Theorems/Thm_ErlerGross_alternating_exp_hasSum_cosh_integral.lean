-- Prove2me | Theorems.Thm_ErlerGross_alternating_exp_hasSum_cosh_integral
-- name    : ErlerGross.alternating_exp_hasSum_cosh_integral
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T18:08:08.654988+00:00
-- url     : https://prove2.me/theorems/e9e5bae4-7b37-4a91-b9ed-232fc37aef33
-- title:
--   Laplace integral representation of the alternating series
-- statement:
--   For complex parameters with |Re a| < Re b, the alternating partial-fraction series is the Laplace integral of cosh(a t)/cosh(b t) over t > 0. This is the termwise Laplace representation followed by a geometric-series summation.
-- source:
--   Laplace-transform reduction of the alternating partial-fraction series in Erler and Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199, Appendix B, p. 45.

import Mathlib
open Real Filter Topology MeasureTheory

namespace ErlerGross
theorem alternating_exp_hasSum_cosh_integral (a b : ℂ)
    (hab : |a.re| < b.re) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n *
      (1 / (((2 * n + 1 : ℕ) : ℂ) * b - a) +
       1 / (((2 * n + 1 : ℕ) : ℂ) * b + a)))
      (∫ t in Set.Ioi (0 : ℝ),
        Complex.cosh (a * (t : ℂ)) / Complex.cosh (b * (t : ℂ))) := by sorry
end ErlerGross
