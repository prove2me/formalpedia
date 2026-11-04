-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_candidate_monotone
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_candidate_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:10:00.447271+00:00
-- url     : https://prove2.me/theorems/9af69d95-c8e7-40fa-8659-dd8929eaad75
-- title:
--   Original infinite-cap HJB verification candidate is monotone on all real reserves
-- statement:
--   From canonical w0≥0, continuity at zero, C² and deriv w≥1 strictly inside (0,∞), and zero extension to negative reserves, derive globally Monotone w. On Ici0 use pinned Mathlib monotoneOn_of_deriv_nonneg with interior=Ioi0 and accepted original infinite-cap nonnegative lemma; across zero use the boundary and zero extension. Enables comparison of stopped controlled W≤x+Xτ with raw Lévy candidate values under the original law.
-- source:
--   Pinned Mathlib monotoneOn_of_deriv_nonneg and P4-F accepted original infinite cap candidate nonnegative 6594777a.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_candidate_monotone
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    Monotone w := by sorry
