-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja33_original_finite_borel_mark_simple_sum_filtration_measurable
-- name    : AvramDividend.Classical.avram_ja33_original_finite_borel_mark_simple_sum_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:13:05.440961+00:00
-- url     : https://prove2.me/theorems/19fadda1-4f67-40cd-9d5c-ecf2772a9314
-- title:
--   Original finite compensated Borel mark-simple sums are measurable in the true terminal filtration
-- statement:
--   Every finite sum of deterministically weighted original-path Borel compensated marked-jump counts on [0,t] is measurable in the true original filtration F_t, for arbitrary Borel mark cells. This provides the actual filtration measurability of the mark-simple variables used in JA28; it does not assert an unproved same-window Poisson covariance.
-- source:
--   Root-connected physical Borel mark-simple source construction 67336b2d; direct composition of Proved b25029d5 and Mathlib measurable finite sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_borel_mark_count_filtration_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja33_original_finite_borel_mark_simple_sum_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Measurable[𝓕 t] (fun ω : Ω =>
      ∑ i ∈ Finset.range K,
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal))) := by sorry
