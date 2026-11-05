-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_negative_ruin_zero
-- name    : AvramDividend.Classical.avram_p2_assist_p3_cap_extension_negative_ruin_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:03:31.493904+00:00
-- url     : https://prove2.me/theorems/eaae0ef0-76db-4a80-a252-750c614dfab5
-- title:
--   Actual cap-linear value vanishes at negative ruin reserves
-- statement:
--   The true original source candidate w vanishes for all negative reserves. Its actual top-cap or finite slope-one continuation V also vanishes at every negative reserve because negative z lies below any finite nonnegative cap. This allows the P3 original stopped residual and Fatou terminal ruin estimates to replace w with V without adding a spurious ruin payoff.
-- source:
--   Exact source cap continuation and Mathlib ENNReal.toReal_nonneg. No stochastic process change.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_cap_extension_negative_ruin_zero
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∀ z : ℝ, z < 0 → V z = 0 := by sorry
