-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_mark_thinning_variance_vanishes_under_source_isometry_bound
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_mark_thinning_variance_vanishes_under_source_isometry_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:49:38.870636+00:00
-- url     : https://prove2.me/theorems/769dd9c9-42f7-4ea8-b442-6829d2362fdb
-- title:
--   Original-source small-jump stochastic error second moments vanish under explicit source variance bound
-- statement:
--   For the original spectrally negative Levy process X on the original probability space, and the genuine right-continuous predictable clock, shrinking negative mark sets have vanishing linear small-jump quadratic energy. Any sequence Y of original-source random variables whose P-second-moment is bounded by this exact predictable source energy therefore has second moment tending to zero. The bound is an explicit isometry/variance hypothesis: this lemma does not establish original-source stochastic integration, compensator identities, or zero expectation.
-- source:
--   Accepted genuine original-source predictable L2 mark thinning d344c3e6, plus Mathlib ordered-filter squeeze theorem; conditional only on an explicit original-P variance estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_mark_thinning_variance_vanishes_under_source_isometry_bound
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
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (Y : ℕ → Ω → ℝ)
    (hYbound : ∀ n,
      (∫⁻ ω, ENNReal.ofReal ((Y n ω)^2) ∂P) ≤
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
          (fun r : ((ℝ≥0 × Ω) × ℝ) =>
            ENNReal.ofReal ((g r.1 * r.2)^2)) p
        ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) :
    Tendsto (fun n : ℕ =>
      (∫⁻ ω, ENNReal.ofReal ((Y n ω)^2) ∂P)) atTop (𝓝 0) := by sorry
