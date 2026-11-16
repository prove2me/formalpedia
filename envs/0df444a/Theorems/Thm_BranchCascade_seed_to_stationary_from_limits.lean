-- Prove2me | Theorems.Thm_BranchCascade_seed_to_stationary_from_limits
-- name    : BranchCascade.seed_to_stationary_from_limits
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:51:39.821503+00:00
-- url     : https://prove2.me/theorems/fad8165e-1961-450f-81e4-8a29b76f4aaa
-- title:
--   Negative seed produces a stationary minimum from endpoint limits
-- statement:
--   Let f be continuous and differentiable on (0,∞), with f(u)→0 as u→0⁺ and f(u)→+∞ as u→∞. If f(x)<0 for some x>0, then
--   $$\exists u>0:\ f(u)<0,\quad f'(u)=0.$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchCascade.seed_to_stationary_from_limits     (f : ℝ → ℝ) (x : ℝ) (hx0 : 0 < x) (hx : f x < 0)
    (hc : ContinuousOn f (Ioi 0)) (hd : DifferentiableOn ℝ f (Ioi 0))
    (hleft : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hright : Tendsto f atTop atTop) :
    ∃ u > 0, f u < 0 ∧ deriv f u = 0 := by sorry
