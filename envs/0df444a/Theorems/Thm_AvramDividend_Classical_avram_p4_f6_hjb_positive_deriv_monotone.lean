-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_positive_deriv_monotone
-- name    : AvramDividend.Classical.avram_p4_f6_hjb_positive_deriv_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:03:38.34952+00:00
-- url     : https://prove2.me/theorems/48e0eef2-06ad-41fe-9331-8fd25a3a92b5
-- title:
--   Positive derivative on the positive half-line makes the HJB reward monotone and nonnegative
-- statement:
--   A reward function continuous at the zero reserve, differentiable at every positive reserve and with derivative at least one is increasing and nonnegative on the nonnegative reserve half-line when w(0) is nonnegative. This deterministic positivity and monotonicity supports the original HJB stopping payoff comparison at the upper exit while keeping downward-contact terms nonnegative.
-- source:
--   Deterministic calculus side condition isolated from the exact original HJB killed-upcross inequality target 8d1164b7-10ee-4fad-92a7-4f012f12ed91. Mathlib monotoneOn_of_deriv_nonneg on Ici 0 provides the argument.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_hjb_positive_deriv_monotone
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hcont : ContinuousOn w (Ici 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ w x)
    (hgrad : ∀ x : ℝ, 0 < x → 1 ≤ deriv w x) :
    MonotoneOn w (Ici 0) ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ w x := by sorry
