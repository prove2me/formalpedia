-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_mono
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_mark_mean_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:57:42.552347+00:00
-- url     : https://prove2.me/theorems/f5268c75-9ce2-45e6-b163-789aaf18dd85
-- title:
--   Actual original source marked-count mean is monotone in Borel mark sets
-- statement:
--   For the exact original Lévy sample space and its genuine intrinsic jump count, prove that the finite-horizon expected number of jumps in a measurable mark B is at most that in any measurable superset C, using the previously Proved original Borel mean-measure representation and measure monotonicity. No ν rate or compensator assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_mark_mean_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : B ⊆ C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) ≤
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ C) ∂P) := by sorry
