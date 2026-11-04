-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
-- name    : AvramDividend.Classical.avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:53:28.338943+00:00
-- url     : https://prove2.me/theorems/9893589a-10b8-4f78-95cb-13aae45b4975
-- title:
--   Original zero-extended continuous verification value admits one uniform finite-cap bound including negative ruin overshoots
-- statement:
--   The precise original UBV candidate hypotheses ContinuousOn w (Ici 0) and w(y)=0 at y<0 imply one real uniform absolute bound on all y≤c when c is a finite real cap. The compact nonnegative interval is controlled by continuous image compactness; negative overshoot is controlled exactly by the source zero-extension. This is a deterministic boundary integrability input for original stopped Term, not an Ito formula or a claim for C=∞.
-- source:
--   Canonical 0dda1be7 verification candidate assumptions; P4-E discounted-terminal integrability conditional 782559c6-2b21-4f34-8078-d096ce603f57; pinned Mathlib compact continuous-image bound.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, y ≤ c → |w y| ≤ B := by sorry
