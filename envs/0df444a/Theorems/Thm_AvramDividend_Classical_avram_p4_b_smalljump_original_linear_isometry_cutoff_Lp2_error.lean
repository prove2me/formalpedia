-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_linear_isometry_cutoff_Lp2_error
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_linear_isometry_cutoff_Lp2_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:44:24.574385+00:00
-- url     : https://prove2.me/theorems/2415d009-01b4-4a0c-b87c-8dc06803eff3
-- title:
--   Original predictable linear small-jump finite-cutoff L2 error under an explicit source isometry
-- statement:
--   For the original spectrally negative Lévy source, its right-continuous predictable L² small-negative linear-mark kernel g(t,ω)z, and an arbitrary measurable finite cutoff A on the actual time-space/mark product, suppose an L² compensated stochastic-integral map I into L²(P) is norm-preserving. Then the L² discrepancy between the I-image of the cutoff integrand and I-image of the full integrand is controlled by the genuine source Lévy-product L² norm of the complement kernel. The isometry is explicitly hypothesised; no original jump-compensator result is asserted.
-- source:
--   Accepted genuine source small-negative MemLp theorem; measure-theoretic indicator decomposition, Lp norm bound and the explicit isometry, following source-verified Avram Wave 6 cutoff Lp2 pattern.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_linear_isometry_cutoff_Lp2_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => g p.1 * p.2;
      let hML : MemLp G (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) :=
        avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
          X μ g hgm hgL2;
      ∀ (A : Set ((ℝ≥0 × Ω) × ℝ)) (hA : MeasurableSet A)
        (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      ‖I ((hML.indicator hA).toLp (A.indicator G)) -
        I (hML.toLp G)‖ ≤
          (eLpNorm (Aᶜ.indicator G) (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))).toReal) := by sorry
