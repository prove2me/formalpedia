-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:58:36.773443+00:00
-- url     : https://prove2.me/theorems/10f8419c-39a6-49b7-b2db-ece648231e27
-- title:
--   Discount-weighted original stopped nonlinear source product compensator is the true Lévy generator drift
-- statement:
--   For the original spectrally negative Lévy source X and adapted dividend D, any bounded right-continuous predictable multiplicative time-weight a preserves joint L1 integrability of the actual stopped nonlinear C² Taylor source jump kernel against μ times original X.ν on all negative marks. Its signed product mass equals the weighted clock integral of the source X.generator nonlinear jump drift. In particular the discount factor exp(-q time), q≥0, satisfies the boundedness requirement once its predictable measurability is supplied. No abstract Poisson compensator or control independence assumption is introduced.
-- source:
--   Proved source-specific product Fubini integral theorem, Proved exact original stopped Taylor-to-generator section identity, original source negative SFinite, Mathlib Integrable.bdd_mul and integral_prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_product_compensator_generator_drift_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
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
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     Integrable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1 * HS p)
       (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     (∫ p : ((ℝ≥0 × Ω) × ℝ), a p.1 * HS p
       ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
       ∫ p : ℝ≥0 × Ω,
         a p * (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) ∂μ) := by sorry
