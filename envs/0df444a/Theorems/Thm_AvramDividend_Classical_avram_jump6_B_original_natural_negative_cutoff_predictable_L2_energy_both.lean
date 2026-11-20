-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_natural_negative_cutoff_predictable_L2_energy_both
-- name    : AvramDividend.Classical.avram_jump6_B_original_natural_negative_cutoff_predictable_L2_energy_both
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:02:53.485483+00:00
-- url     : https://prove2.me/theorems/cfdedb7d-b6f8-4b70-8a65-3e37fe676768
-- title:
--   Original infinite-activity shrinking negative-mark natural cutoff predictable L2 energy and eLpNorm vanish
-- statement:
--   For the actual Levy source and any predictable square-integrable coefficient g and predictable clock measure, the true z-weighted small negative mark integrand restricted to Ioo(-1/(n+1),0) has squared compensator mass and eLpNorm L2 tending to zero. This is the genuine natural source mark cutoff for any jump activity and uses the proved original predictable L2 thinning and norm tail theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_natural_negative_cutoff_predictable_L2_energy_both
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    let B : ℕ → Set ℝ := fun n =>
      Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ);
    Tendsto (fun n : ℕ => (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      ({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
        (fun r => ENNReal.ofReal ((g r.1 * r.2)^2)) p
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) atTop (𝓝 (0 : ℝ≥0∞)) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Tendsto (fun n : ℕ =>
        eLpNorm
          (({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
            (fun r : ((ℝ≥0 × Ω) × ℝ) => g r.1 * r.2))
          (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))
        atTop (𝓝 (0 : ℝ≥0∞)))
 := by sorry
