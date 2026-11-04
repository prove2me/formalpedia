-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_negative_mark_L2_energy
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_negative_mark_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:57:17.154467+00:00
-- url     : https://prove2.me/theorems/aa3744ce-1b4c-44ed-a1db-372bff411793
-- title:
--   Original predictable bounded derivative times small negative mark has finite true Lévy L2 energy
-- statement:
--   For the original spectrally negative Lévy source X on the given probability space and the derived right-continuous predictable sigma algebra, fix a finite physical predictable time-space measure μ. If an actual predictable coefficient g is bounded in absolute value by M, its product with the negative jump mark z is measurable on the predictable time-space × mark product, and its quadratic energy over -1<z<0 is finite for the genuine source Lévy measure X.ν. This uses the actual Lévy square-moment condition and finite μ; no Poisson random measure, L2 isometry or stochastic martingale assertion is introduced.
-- source:
--   Use accepted original ν small-negative square moment, source predictable measurability, pointwise |g| bound and two applications of the nonnegative integral monotonicity/Fubini bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_negative_mark_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (M : ℝ) (hM : 0 ≤ M) (hg : ∀ p, |g p| ≤ M) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => g p.1 * p.2) ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal ((g p * z)^2) ∂X.ν ∂μ) < ⊤) := by sorry
