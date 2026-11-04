-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_canonical_negative_linear_L2_tail_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_negative_linear_L2_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:10:21.730432+00:00
-- url     : https://prove2.me/theorems/3071a257-5b30-4c87-8401-7469c9604fcb
-- title:
--   Original-source predictable linear small-negative Lévy L2 energy vanishes on canonical near-zero intervals
-- statement:
--   Under the genuine source SpectrallyNegativeLevy X, a measurable coefficient g in its right-continuous predictable filtration with finite quadratic energy produces vanishing predictable small-jump linear energy in the explicit negative intervals (-1/(n+1),0). This supplies the infinite-activity cutoff limit directly, without a finite first moment or an artificial Poisson source. It does not assert the original compensated jump integral exists.
-- source:
--   The accepted original-source predictable L2 mark-thinning theorem and independently proved canonical negative mark geometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_negative_linear_L2_tail_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    Tendsto (fun n : ℕ =>
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ({r : ((ℝ≥0 × Ω) × ℝ) |
          r.2 ∈ Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ)}).indicator
          (fun r : ((ℝ≥0 × Ω) × ℝ) =>
            ENNReal.ofReal ((g r.1 * r.2)^2)) p
        ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) atTop (𝓝 0) := by sorry
