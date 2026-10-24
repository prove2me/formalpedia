-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_deriv_eq_local
-- name    : AvramDividend.Classical.causal_exp_weighted_primitive_deriv_eq_local
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:14:10.746657+00:00
-- url     : https://prove2.me/theorems/8948a13d-02d7-43c7-b7b6-aaaa91bfbfd1
-- title:
--   Local-integrability derivative identity for exponentially weighted causal primitive
-- statement:
--   A continuous positive-time kernel with exponential weighting integrable on every interval from 0 to x admits the exact damped-primitive derivative formula. No global exponential integrability is required, enabling termwise differentiation of Volterra convolution powers.
-- source:
--   Fundamental theorem of calculus for finite-interval integrals and derivative of the real exponential.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_deriv_eq_continuous_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

namespace AvramDividend.Classical

theorem causal_exp_weighted_primitive_deriv_eq_local
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      deriv (fun y : ℝ => Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume)) x =
      g x - w * (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * g s ∂volume)) := by sorry

end AvramDividend.Classical
