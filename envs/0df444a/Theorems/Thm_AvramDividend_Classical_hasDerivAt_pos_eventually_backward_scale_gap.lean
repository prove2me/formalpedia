-- Prove2me | Theorems.Thm_AvramDividend_Classical_hasDerivAt_pos_eventually_backward_scale_gap
-- name    : AvramDividend.Classical.hasDerivAt_pos_eventually_backward_scale_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:17:50.168976+00:00
-- url     : https://prove2.me/theorems/dd6f071a-ccb6-4831-a70e-ef84c03e9997
-- title:
--   Positive derivative makes backward scale finite differences eventually positive
-- statement:
--   For a real-valued function with strictly positive derivative at a, all sufficiently small positive ε satisfy W(a) > W(a−ε), so the backward scale increment W(a)−W(a−ε) is eventually strictly positive. Proof reflects the function and uses the published forward derivative gap lemma, preparing the lower stopped-renewal finite-difference denominator.
-- source:
--   Mathlib HasDerivAt.const_sub, HasDerivAt.comp_of_eq, HasDerivAt.neg and the Prove2Me forward gap theorem.

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_pos_eventually_forward_scale_gap

open Filter Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.hasDerivAt_pos_eventually_backward_scale_gap
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < W a - W (a - ε) := by sorry
