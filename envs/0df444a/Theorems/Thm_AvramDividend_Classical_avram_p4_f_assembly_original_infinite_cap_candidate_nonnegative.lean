-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:36:09.101596+00:00
-- url     : https://prove2.me/theorems/6594777a-b990-4608-ad17-660b00b8b5f1
-- title:
--   Canonical infinite-cap candidate is globally nonnegative from interior C2, gradient and zero extension
-- statement:
--   When canonical C=∞, every finite positive reserve lies strictly in the permitted interior. The canonical C2/gradient hypotheses thus give a nonnegative derivative on each compact positive interval. The accepted P4-E boundary monotonicity lemma and continuity from zero yield w≥0 on all nonnegative reserves; negative values are exactly zero by original extension. This is a needed nonnegative terminal input for source Fatou/localisation at unbounded cap, with no stochastic moment assumption.
-- source:
--   Accepted P4-E 4da8dd65 boundary payoff, canonical w0, smooth, gradient and negative extension; pinned Mathlib ContDiffOn.differentiableOn and ENNReal.ofReal_lt_top.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_infinite_cap_candidate_nonnegative
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ w y := by sorry
