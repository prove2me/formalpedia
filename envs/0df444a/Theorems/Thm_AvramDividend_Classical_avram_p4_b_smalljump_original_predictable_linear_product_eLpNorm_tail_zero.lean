-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:07:33.121147+00:00
-- url     : https://prove2.me/theorems/1ecaac48-24c4-4e07-801d-be39caf94b71
-- title:
--   Original predictable small-negative Lévy L2 seminorm vanishes along arbitrary shrinking mark bands
-- statement:
--   For the genuine source X, arbitrary square-integrable coefficient measurable in 𝓕.rightCont.predictable, and any decreasing measurable negative mark bands with empty intersection, the actual product measure eLpNorm2 of the thinned linear small-jump kernel g(t,ω)z tends to zero. This strengthens the accepted ENNReal square-energy thinning result to the genuine MemLp2 seminorm, suitable for a norm-preserving original compensated-jump integration map. It asserts no such map exists.
-- source:
--   Accepted original small-negative product MemLp and original predictable L2 energy thinning, pinned Mathlib eLpNorm integral representation and ENNReal continuity of real powers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Tendsto (fun n : ℕ =>
        eLpNorm
          (({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
            (fun r : ((ℝ≥0 × Ω) × ℝ) => g r.1 * r.2))
          (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))
        atTop (𝓝 0)) := by sorry
