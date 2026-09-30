-- Prove2me | Theorems.Thm_ErlerGross_cosh_ratio_integral_evaluation
-- name    : ErlerGross.cosh_ratio_integral_evaluation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T18:08:11.433486+00:00
-- url     : https://prove2.me/theorems/521d5b2f-be32-40a2-ba04-d97c36836d4e
-- title:
--   Integral of a hyperbolic-cosine ratio
-- statement:
--   For complex parameters a and b with |Re a| < Re b, the integral of cosh(a t)/cosh(b t) on the positive real axis equals π/(2b cos(πa/(2b))).
-- source:
--   Classical hyperbolic-secant transform used to evaluate the integral in Erler and Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199, Appendix B, p. 45.

import Mathlib
open Real Filter Topology MeasureTheory

namespace ErlerGross
theorem cosh_ratio_integral_evaluation (a b : ℂ)
    (hab : |a.re| < b.re) :
    (∫ t in Set.Ioi (0 : ℝ),
      Complex.cosh (a * (t : ℂ)) / Complex.cosh (b * (t : ℂ))) =
      (Real.pi : ℂ) / (2 * b) *
        (1 / Complex.cos ((Real.pi : ℂ) * a / (2 * b))) := by sorry
end ErlerGross
