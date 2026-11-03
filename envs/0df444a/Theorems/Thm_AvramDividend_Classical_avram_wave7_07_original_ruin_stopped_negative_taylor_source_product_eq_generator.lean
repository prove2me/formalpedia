-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ruin_stopped_negative_taylor_source_product_eq_generator
-- name    : AvramDividend.Classical.avram_wave7_07_original_ruin_stopped_negative_taylor_source_product_eq_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:25:35.812959+00:00
-- url     : https://prove2.me/theorems/39476301-0701-4001-bbe2-d5056bcc581f
-- title:
--   Original controlled ruin-stopped nonlinear negative Lévy jump product drift equals generator
-- statement:
--   For the original spectrally negative Lévy process X, actual Ω,P and dividend strategy D, prove the Bochner product integral of its ruin-stopped prepayment C2 negative jump Taylor correction over any finite predictable clock μ and source negative jump measure equals the iterated genuine truncated Lévy generator mark integral. Unweighted and unthinned source interface suitable for stopped Itô–Meyer.
-- source:
--   W7-07 direct unweighted original source C2 jump compensation contribution; consumer W7-08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_unit_thinned_generator_drift_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ruin_stopped_negative_taylor_source_product_eq_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∫ r : ((ℝ≥0 × Ω) × ℝ), HS r ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
    (∫ p : ℝ≥0 × Ω,
      (∫ z in Iio (0 : ℝ), G (p,z) ∂X.ν) ∂μ) := by sorry
