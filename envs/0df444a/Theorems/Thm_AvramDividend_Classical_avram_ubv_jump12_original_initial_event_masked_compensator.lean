-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_masked_compensator
-- name    : AvramDividend.Classical.avram_ubv_jump12_original_initial_event_masked_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T18:13:59.843901+00:00
-- url     : https://prove2.me/theorems/f93037de-cd83-485b-894b-8ce9e12ef0e4
-- title:
--   Original real-time negative-jump compensator commutes with initial-event clock masking
-- statement:
--   For the original Lévy negative-mark compensator under real Lebesgue time mapped to nonnegative time, masking the stopped clock by an initial event masks the double jump compensator integral pathwise. The source clock has no atom at time zero, so the zero-clock contribution vanishes, regardless of infinite small-jump intensity.
-- source:
--   Original physical-clock complement to the initial-event masked sample-path jump-integral lemma, intended to transfer canonical stopped Taylor martingale centring to the eventwise positive-clock source budget 0b1a879a-c9c5-4d2c-9039-a143ec7db5dc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_jump12_original_initial_event_masked_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (A : Set Ω) (σ : Ω → ℝ≥0)
    (H : Ω → ℝ≥0 → ℝ → ℝ) :
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    ∀ ω,
      (∫ t, ∫ z, (if t ≤ A.indicator σ ω then H ω t z else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT) =
      A.indicator (fun ξ =>
        ∫ t, ∫ z, (if t ≤ σ ξ then H ξ t z else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT) ω := by sorry
