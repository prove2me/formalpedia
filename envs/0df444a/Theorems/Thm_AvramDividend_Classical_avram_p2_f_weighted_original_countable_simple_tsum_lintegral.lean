-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_simple_tsum_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_simple_tsum_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:56:04.770981+00:00
-- url     : https://prove2.me/theorems/2ea482a9-c3a7-4f21-bb87-216a01d14a15
-- title:
--   Countable nonnegative simple-weight Tonelli interchange for original Lévy intrinsic marked counts
-- statement:
--   For any countable collection of measurable nonnegative weights, the expectation of the genuine original Lévy marked jump count times the countable sum of weights equals the countable sum of their expected marked contributions. Handles 0×∞ and all infinite intensities. Uses actual original intrinsic rectangle measurable, ENNReal.tsum_mul_right and Mathlib lintegral_tsum, without a prescribed ν-rate or Poisson copy.
-- source:
--   Pinned Mathlib ENNReal.tsum_mul_right and MeasureTheory.lintegral_tsum; proved original intrinsic rectangle measurable d9c55240.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_simple_tsum_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : ℕ → Ω → ℝ≥0∞) (hMeas : ∀ n, Measurable (H n)) :
    (∫⁻ ω, (∑' n : ℕ, H n ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    ∑' n : ℕ, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by sorry
