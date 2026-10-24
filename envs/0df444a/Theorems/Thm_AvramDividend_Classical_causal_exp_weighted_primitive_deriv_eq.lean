-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_deriv_eq
-- name    : AvramDividend.Classical.causal_exp_weighted_primitive_deriv_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:54:31.993074+00:00
-- url     : https://prove2.me/theorems/03ab41c0-ba7f-40aa-a02f-60e2bbae9cc0
-- title:
--   Exact derivative of a damped causal primitive of a positive-time L1 function
-- statement:
--   For a kernel g whose exponentially weighted version exp(w·s)g(s) is L1 and continuous at positive times, the derivative of exp(−wx)∫_0^x exp(ws)g(s)ds is g(x)−w times the weighted primitive. This is the termwise derivative identity for the exponentially damped Volterra Neumann series.
-- source:
--   Fundamental theorem of calculus for continuous positive-time L1 primitives, real exponential derivative and Leibniz product rule.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_deriv_eq_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_primitive_contDiff_one

open AvramDividend.Classical MeasureTheory Set
open scoped Topology

namespace AvramDividend.Classical

theorem causal_exp_weighted_primitive_deriv_eq
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : IntegrableOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ)) volume)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      deriv (fun y : ℝ => Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume)) x =
      g x - w * (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * g s ∂volume)) := by sorry

end AvramDividend.Classical
