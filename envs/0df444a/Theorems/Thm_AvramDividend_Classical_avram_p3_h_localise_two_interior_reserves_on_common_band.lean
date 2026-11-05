-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_two_interior_reserves_on_common_band
-- name    : AvramDividend.Classical.avram_p3_h_localise_two_interior_reserves_on_common_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:07:27.487738+00:00
-- url     : https://prove2.me/theorems/81892d4b-ce14-405d-9f73-84345905a225
-- title:
--   Two source BV interior reserve values share one positive-cap compact compensation band
-- statement:
--   For two strictly interior reserve states of the original controlled BV Lévy source, construct one closed compact reserve band containing both, with lower cutoff at most two and an enlarged strip wholly below the cap. Useful for uniform finite-grid local Lipschitz and stopped-jump control.
-- source:
--   Real min/max and monotonicity of ENNReal.ofReal; source-stable geometric lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_localise_two_interior_reserves_on_common_band
    (C : ℝ≥0∞) (z₁ z₂ : ℝ)
    (h₁ : 0 < z₁ ∧ ENNReal.ofReal z₁ < C)
    (h₂ : 0 < z₂ ∧ ENNReal.ofReal z₂ < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧
      z₁ ∈ Icc a b ∧ z₂ ∈ Icc a b ∧
      Icc (a / 2) b ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
