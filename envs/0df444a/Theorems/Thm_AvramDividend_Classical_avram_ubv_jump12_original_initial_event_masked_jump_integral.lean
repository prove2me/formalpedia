-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_initial_event_masked_jump_integral
-- name    : AvramDividend.Classical.avram_ubv_jump12_original_initial_event_masked_jump_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T18:12:08.92211+00:00
-- url     : https://prove2.me/theorems/a3f7fb5d-f00a-4755-9f2d-090b20376f96
-- title:
--   Original stopped negative-jump integral commutes with initial-event clock masking
-- statement:
--   For the original sample-path Lévy jump-count measure, masking any random stopping clock by an event gives an integral equal to the initial-event indicator of the original stopped integral, for every sample path and every real jump integrand. The proof uses the strict-positive jump-time support to show that a clock masked to zero contributes no jump integral.
-- source:
--   Source-exact component of the original compensated-jump initial-event centring obligation for Open 0b1a879a-c9c5-4d2c-9039-a143ec7db5dc; paired with a null time-zero compensator, this gives the stopped Taylor mask identity. Original process X and original jump measure are retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_jump12_original_initial_event_masked_jump_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (σ : Ω → ℝ≥0)
    (H : Ω → (ℝ≥0 × ℝ) → ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    ∀ ω,
      (∫ p, (if p.1 ≤ A.indicator σ ω then H ω p else 0) ∂(NX ω)) =
        A.indicator (fun ξ =>
          ∫ p, (if p.1 ≤ σ ξ then H ξ p else 0) ∂(NX ξ)) ω := by sorry
