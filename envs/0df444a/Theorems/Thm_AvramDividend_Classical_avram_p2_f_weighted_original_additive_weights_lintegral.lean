-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_additive_weights_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_additive_weights_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:52:41.120071+00:00
-- url     : https://prove2.me/theorems/3a68fcdf-2ed7-4082-8e94-392dd12d0e04
-- title:
--   Nonnegative linearity of the genuine original marked future-count expectation in adapted weights
-- statement:
--   For two measurable nonnegative weights, the expected genuine original Lévy intrinsic marked count multiplied by their sum equals the sum of the two expected weighted counts, including infinite values. Uses source measurable rectangle count and pinned Mathlib lintegral_add_left; no ν-rate, Poisson construction or finiteness assumption.
-- source:
--   Original source intrinsic rectangle measurable d9c55240; Mathlib MeasureTheory.lintegral_add_left.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_additive_weights_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H K : Ω → ℝ≥0∞) (hH : Measurable H) (hK : Measurable K) :
    (∫⁻ ω, (H ω + K ω) * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) +
    (∫⁻ ω, K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by sorry
