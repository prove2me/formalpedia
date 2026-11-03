-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_negative_count_compensated_L1_zero_mean
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_negative_count_compensated_L1_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:56:38.670091+00:00
-- url     : https://prove2.me/theorems/77c1aead-6fb2-4ad0-8a7a-0e5603f9606e
-- title:
--   Original BV negative-jump predictable rectangle has integrable real compensated increment with zero expectation
-- statement:
--   For the unchanged original spectrally negative Levy source Ω,P,𝓕,X, an adapted finite-horizon negative-mark count with a genuine measurable future-path extractor has integrable real compensated increment and exactly zero expectation. Uses the proved original finite-activity ENNReal predictor, with explicit nonnegativity/measurability/finite-L1 localisation; this is a finite-simple martingale increment and does not assert the full signed C1 jump-kernel compensation or stopped Ito identity.
-- source:
--   Proved original adapted negative-mark compensation bb47482c-4294-4845-8598-159248fa0493; pinned Mathlib integral_toReal and integrable_toReal_iff transfer nonnegative extended expectations to real L1 without assuming zero-mean of the compensated increment. Separate real finite-activity localisation step for W8-04's expectation bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_negative_count_compensated_L1_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hHadapt : Measurable[𝓕 s] H)
    (hHm : Measurable H)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (N : Ω → ℝ≥0∞)
    (hN : ∀ ω : Ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)))
    (hExtract : ∀ ω : Ω,
      N ω = F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω))
    (hJm : AEMeasurable (fun ω => H ω * N ω) P)
    (hJae : ∀ᵐ ω ∂P, H ω * N ω < ⊤)
    (hKae : ∀ᵐ ω ∂P,
      H ω * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) < ⊤)
    (hKfin : (∫⁻ ω, H ω *
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) ∂P) < ⊤) :
    Integrable (fun ω =>
      (H ω * N ω).toReal -
      (H ω * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)))).toReal) P ∧
    (∫ ω, ((H ω * N ω).toReal -
      (H ω * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)))).toReal) ∂P) = 0 := by sorry
