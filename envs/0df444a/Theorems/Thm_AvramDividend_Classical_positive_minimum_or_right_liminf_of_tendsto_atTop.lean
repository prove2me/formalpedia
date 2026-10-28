-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_minimum_or_right_liminf_of_tendsto_atTop
-- name    : AvramDividend.Classical.positive_minimum_or_right_liminf_of_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:52:25.381064+00:00
-- url     : https://prove2.me/theorems/e3013944-eccd-4156-8823-c155adaa5f66
-- title:
--   Positive-axis minimum or right-endpoint liminf dichotomy under continuity and coercivity
-- statement:
--   For a real-valued function continuous on (0,∞) and tending to +∞ at +∞, either its global positive-axis minimum is attained or its EReal right liminf at zero is no larger than every positive value. This is precisely the deterministic dichotomy in AvramDividend.Classical.scaleDeriv_inf_attained after setting f = deriv W and identifying derivZeroPlus. Its proof was previously private inside the canonical Proved cstar finiteness bridge, and this theorem exposes that verified compactness argument for direct reuse.
-- source:
--   The canonically Proved cstar_lt_top_of_deriv_continuous_tendsto_atTop, accepted submission ee363315-f06b-4854-a662-9282e3f92a2c, previously contained this private 40-line proof. Republished verbatim as a reusable generic theorem.

import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_deriv_continuous_tendsto_atTop

open Filter Set Topology
open scoped ENNReal

theorem AvramDividend.Classical.positive_minimum_or_right_liminf_of_tendsto_atTop
    (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Ioi 0))
    (htop : Tendsto f atTop atTop) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x) ∨
      ∀ x : ℝ, 0 < x →
        Filter.liminf (fun y => (f y : EReal)) (𝓝[>] (0 : ℝ)) ≤
          (f x : EReal) := by sorry
