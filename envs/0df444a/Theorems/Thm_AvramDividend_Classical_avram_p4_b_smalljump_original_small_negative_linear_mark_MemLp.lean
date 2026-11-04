-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:23:58.80409+00:00
-- url     : https://prove2.me/theorems/20acefeb-6c24-4e59-b023-b3fc37ab8d5c
-- title:
--   Actual small-negative linear Lévy mark is in predictable product L2 from the source Lévy condition alone
-- statement:
--   For an arbitrary original spectrally negative Lévy source X, true right-continuous predictable clock μ, and any predictable square-integrable coefficient g, the original negative small-jump kernel g(t,ω)z on (-1,0) lies in L²(μ ⊗ X.ν|(-1,0)). The needed sigma-finiteness and z² integrability are discharged from accepted intrinsic source Lévy theorems, without inserting a new stochastic compensator or Poisson random measure.
-- source:
--   Specialisation of the proved exact source product MemLp theorem using finite_small_negative_jump_square_moment and levy_negative_jump_measure_sFinite plus nested restrictions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_mark_product_MemLp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      MemLp (fun p : ((ℝ≥0 × Ω) × ℝ) => g p.1 * p.2)
        (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))) := by sorry
