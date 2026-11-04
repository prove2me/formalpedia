-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:36:22.655766+00:00
-- url     : https://prove2.me/theorems/d344c3e6-015a-4129-ac9e-5a829797519b
-- title:
--   Genuine predictable original small-negative linear jump quadratic energy vanishes under shrinking mark thinning
-- statement:
--   For the actual source X : SpectrallyNegativeLevy P 𝓕, its original right-continuous predictable clock μ, and a square-integrable predictable coefficient g, let Bₙ be measurable decreasing mark sets with empty intersection. The squared linear small-negative kernel g(t,ω)z, integrated against the genuine product μ⊗X.ν restricted to (-1,0) and further thinned by Bₙ, has quadratic energy tending to zero. This is an unconditional deterministic source L² approximation result; it makes no claim about the intrinsic random jump-measure martingale.
-- source:
--   Accepted original-source L2 coefficient/mark factorisation, original negative Lévy s-finiteness and small square moment, plus the pinned Mathlib antitone dominated-convergence theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_L2_linear_mark_factorisation
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    Tendsto (fun n : ℕ => (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      ({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator (fun r : ((ℝ≥0 × Ω) × ℝ) => ENNReal.ofReal ((g r.1 * r.2)^2)) p
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) atTop (𝓝 0) := by sorry
