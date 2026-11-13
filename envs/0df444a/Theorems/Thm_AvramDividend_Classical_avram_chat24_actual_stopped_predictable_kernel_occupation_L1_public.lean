-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_actual_stopped_predictable_kernel_occupation_L1_public
-- name    : AvramDividend.Classical.avram_chat24_actual_stopped_predictable_kernel_occupation_L1_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:05:40.191611+00:00
-- url     : https://prove2.me/theorems/6c31b920-d196-4959-86e8-866cafb6ea8b
-- title:
--   Original stopped predictable kernel has finite occupation L1
-- statement:
--   General actual-original-X occupation certificate used by the precise regularity certificate for 10ef35ab. Preserve the genuine original jump counting measure and predictable graph lift; prove Measurable H and Integrable H of its original occupation bind. Proved finite-band stopped compensation supplies the restricted occupation L1 fact and stopped support upgrades it. No pathwise integrability is assumed and no outer-RV integral is used as a substitute. Published as a public prerequisite because the authoritative parent is public and public candidates cannot import private helper declarations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_actual_stopped_predictable_kernel_occupation_L1_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) 𝓕.rightCont.predictable)
    (hμfinite : μ univ < ∞)
    (hμclock : ∀ A, MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] G)
    (hGi : Integrable G (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : ℝ≥0∞)))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let Ξ : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ)) :=
      fun ω => @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) inferInstance
        (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable (inferInstance : MeasurableSpace ℝ))
        (fun p => ((p.1, ω), p.2)) (NX ω)
    Measurable[(@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
      (inferInstance : MeasurableSpace ℝ))] H ∧ Integrable H (P.bind Ξ) := by sorry
