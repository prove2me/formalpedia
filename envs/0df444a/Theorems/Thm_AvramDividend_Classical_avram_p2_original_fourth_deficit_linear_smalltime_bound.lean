-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_deficit_linear_smalltime_bound
-- name    : AvramDividend.Classical.avram_p2_original_fourth_deficit_linear_smalltime_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:11:33.161092+00:00
-- url     : https://prove2.me/theorems/d2aca944-446e-430c-b1b9-8295f3f2bac7
-- title:
--   Original Lévy fourth exponential deficit has a locally uniform linear small-time expectation bound
-- statement:
--   For the actual original spectrally negative Lévy process X, the fourth power of exp(X_h)-1 has expected value bounded by a finite positive constant times h for all sufficiently small positive h. This is a quantitative O(h) consequence of the canonical source weighted fourth derivative and supplies uniform grid-tail estimates without any jump compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_fourth_deficit_linear_smalltime_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫ ω, (Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤ C * h := by sorry
