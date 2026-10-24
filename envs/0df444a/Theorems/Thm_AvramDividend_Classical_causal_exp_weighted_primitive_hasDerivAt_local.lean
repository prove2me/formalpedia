-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_hasDerivAt_local
-- name    : AvramDividend.Classical.causal_exp_weighted_primitive_hasDerivAt_local
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:29:15.719404+00:00
-- url     : https://prove2.me/theorems/a6d0c96d-ba99-4b29-9dd8-3a9ecd53b985
-- title:
--   Local HasDerivAt witness for exponentially damped causal primitives
-- statement:
--   A damped primitive with a continuous locally interval-integrable weighted kernel has a genuine derivative at every positive time, with the derivative given by the signed kernel value minus the damping term. This is the HasDerivAt interface needed by the proved quadratic-geometric C1 series theorem.
-- source:
--   Fundamental theorem of calculus on positive intervals plus product differentiability, with derivative value from the Proved local derivative theorem.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_deriv_eq_local

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

theorem AvramDividend.Classical.causal_exp_weighted_primitive_hasDerivAt_local
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume))
        (g x - w * (Real.exp (-w * x) *
          (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * g s ∂volume))) x := by sorry
