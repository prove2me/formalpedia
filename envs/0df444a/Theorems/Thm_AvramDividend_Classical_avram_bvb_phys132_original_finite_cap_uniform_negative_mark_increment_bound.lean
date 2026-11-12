-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
-- name    : AvramDividend.Classical.avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:59:46.473846+00:00
-- url     : https://prove2.me/theorems/e4637f43-7d1c-4462-8299-14944e29b509
-- title:
--   Original finite extended-real dividend cap gives uniform negative-mark bound
-- statement:
--   On the genuine finite ENNReal dividend cap from the original BV physical verification theorem, all strictly negative marked value increments admit one finite uniform bound, independent of the mark. This is the precise bounded domination for its finite activity compensator.
-- source:
--   Proved phys130 compact bound and Mathlib ENNReal.toReal_mono hFinite

import Mathlib
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound (C : ℝ≥0∞) (hFinite : C ≠ ⊤) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ b z : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C → z < 0 → |w (b + z) - w b| ≤ 2 * M := by sorry
