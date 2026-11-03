-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_L1_error_bound
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_L1_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:33:52.032782+00:00
-- url     : https://prove2.me/theorems/db998b7c-e62a-412c-8200-d911b3097b05
-- title:
--   Actual discounted ruin-stopped Taylor arbitrary predictable cutoff has quantitative original-source L1 error bounded by complementary L2 jump energy
-- statement:
--   For the actual spectrally negative Levy process X and admissible controlled dividend strategy D, with inclusive ruin stopping, finite horizon T, discount q >= 0, C2 Taylor negative-jump kernel GW and the original right-continuous predictable product clock, an isometric centred stochastic mapping I has ordinary P-L1 arbitrary-cutoff error bounded by the complementary physical L2 square-energy norm. This does not require finite first moment of small negative jumps.
-- source:
--   The accepted arbitrary source-isometric Lp2 cutoff inequality controls the exact original controlled Taylor product band error. On P, eLpNorm1 is bounded by eLpNorm2 because P is a probability measure; integral_norm_eq_lintegral_enorm converts the eLpNorm1 bound to the ordinary integral of the absolute error. This is a quantitative source-specific L1 localisation bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_Lp2_error_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_source_cutoff_L1_error_bound
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
      ∀ (A : Set (((ℝ≥0 × Ω) × ℝ))) (hA : MeasurableSet A)
        (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      (∫ ω, |((I ((hML.indicator hA).toLp (A.indicator GW)) -
          I (hML.toLp GW)) ω : ℝ)| ∂P) ≤
          (eLpNorm (Aᶜ.indicator GW) (2 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal) := by sorry
