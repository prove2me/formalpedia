-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:57:02.057243+00:00
-- url     : https://prove2.me/theorems/4e7ff26a-a608-4946-8c45-04f3cdbb3efb
-- title:
--   Original Lévy predictable stopped signed grid expectation budget
-- statement:
--   For an original bounded stopped physical grid of a spectrally negative Lévy process, source increments with integrable zero conditional means at their right-continuous physical filtration times, predictable selection events, and nonpositive integrable drift pieces, the selected total signed source is integrable and has nonpositive expected value.
-- source:
--   Original SpectrallyNegativeLevy.isProbability; pinned Mathlib setIntegral_condExp, ae_restrict_of_ae, integral_indicator; independently Proved avram_bv_env3_turn10_original_selected_signed_grid_budget UUID 089c5f1e. All genuine source conditional centering remains an explicit premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn10_original_selected_signed_grid_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hPredictable : ∀ i,
      MeasurableSet[𝓕.rightCont (u i)] {ω : Ω | i < k ω})
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω), (M i ω + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω), (M i ω + B i ω) ∂P) ≤ 0 := by sorry
