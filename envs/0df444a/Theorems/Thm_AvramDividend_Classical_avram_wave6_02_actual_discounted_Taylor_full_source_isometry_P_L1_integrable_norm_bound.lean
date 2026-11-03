-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_Taylor_full_source_isometry_P_L1_integrable_norm_bound
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_Taylor_full_source_isometry_P_L1_integrable_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:31:08.090578+00:00
-- url     : https://prove2.me/theorems/52b7ad95-9c54-4f17-a3c4-7e2793a03a4d
-- title:
--   Full actual ruin-stopped discounted Taylor source isometry image is integrable on P and its L1 absolute norm is bounded by true physical L2 energy
-- statement:
--   For actual original X, 𝓕.rightCont predictable discounted inclusive ruin-stopped C² Taylor GW and original isometric Lp²(P) image I(GW), the full stochastic image is genuinely P-integrable and ∫|I(GW)| dP ≤ eLpNorm₂(GW; μ×ν_-). The finite probability of P justifies L2→L1, not finite raw small-jump first moment or finite total physical Lévy product measure.
-- source:
--   Pin Mathlib MemLp.integrable, eLpNorm_le_eLpNorm_of_exponent_le on P, integral_norm_eq_lintegral_enorm, Lp.norm_toLp, and source isometry hIso.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_Taylor_full_source_isometry_P_L1_integrable_norm_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let hML : MemLp GW (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) :=
        avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
          X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      Integrable (fun ω => (I (hML.toLp GW) ω : ℝ)) P ∧
      (∫ ω, |(I (hML.toLp GW) ω : ℝ)| ∂P) ≤
        (eLpNorm GW (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal) := by sorry
