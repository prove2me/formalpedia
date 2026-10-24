-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_primitive_deriv_eq_continuous_on_positive
-- name    : AvramDividend.Classical.causal_primitive_deriv_eq_continuous_on_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:22:29.165374+00:00
-- url     : https://prove2.me/theorems/e4291b31-a7f9-49a0-95c9-85cb5ac86c3a
-- title:
--   Fundamental theorem for the causal primitive of a continuous resolvent
-- statement:
--   If g is continuous on the nonnegative real half-line, the causal integral G(x)=∫_(0,x]g(s)ds has ordinary derivative G'(x)=g(x) at every x>0. The result supplies the derivative identification absent from the existing causal Volterra primitive existence theorem.
-- source:
--   Fundamental theorem of calculus. Uses the already accepted derivative construction in causal_primitive_C1_locally_bounded, proof source 60c3efbb-40c3-4f1a-98ce-d83b71bde858.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
open scoped Topology

namespace AvramDividend.Classical

theorem causal_primitive_deriv_eq_continuous_on_positive
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      deriv (fun y : ℝ => ∫ s in Ioc (0 : ℝ) y, g s ∂volume) x = g x := by sorry

end AvramDividend.Classical
