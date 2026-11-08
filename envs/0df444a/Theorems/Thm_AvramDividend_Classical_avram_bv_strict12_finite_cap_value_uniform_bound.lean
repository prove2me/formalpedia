-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_finite_cap_value_uniform_bound
-- name    : AvramDividend.Classical.avram_bv_strict12_finite_cap_value_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:31:51.621776+00:00
-- url     : https://prove2.me/theorems/f1996785-7d2c-45b0-9ee5-35387bd17c09
-- title:
--   Finite dividend surplus cap bounds the continuous candidate uniformly
-- statement:
--   For the original finite-cap dividend verification problem, continuity of w on nonnegative surplus gives a uniform absolute bound on the entire bounded nonnegative cap region.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict12_finite_cap_value_uniform_bound
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → |w y| ≤ K := by sorry
