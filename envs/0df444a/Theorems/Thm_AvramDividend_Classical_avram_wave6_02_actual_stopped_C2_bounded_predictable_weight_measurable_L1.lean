-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_bounded_predictable_weight_measurable_L1
-- name    : AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_bounded_predictable_weight_measurable_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:33:08.928963+00:00
-- url     : https://prove2.me/theorems/57cc0522-0d76-4b79-8785-ed18eb5f75d4
-- title:
--   Actual ruin-stopped controlled C² Taylor kernel multiplied by any bounded predictable weight remains jointly predictable and L¹ on the true negative Lévy intensity
-- statement:
--   On the actual spectrally negative Lévy source, the original ruin-inclusively-stopped controlled C² Taylor jump remainder multiplied by an arbitrary bounded right-continuous predictable state/time weight is jointly predictable and integrable against the authentic finite predictable occupation measure times negative Lévy intensity, including infinite small-jump activity. The result directly supplies the two analytic prerequisites for source-exact stopped L1 compensation.
-- source:
--   Canonical Proved actual controlled Taylor predictability and full-negative-mark energy theorem 0e0663b1; canonical Proved arbitrary bounded predictable weight product-source generator integration theorem 10f8419c; used as prerequisite to b82b90ec original source centred compensation; no substitute process or unproved Poisson law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_bounded_predictable_weight_measurable_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (a : (ℝ≥0 × Ω) → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (M : ℝ) (haBound : ∀ p, |a p| ≤ M) :
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] GW ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     Integrable GW (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
