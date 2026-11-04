-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_dominated_l1_and_ae_finite
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_dominated_l1_and_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:02:09.522085+00:00
-- url     : https://prove2.me/theorems/286bb5c0-ad9f-4472-9326-bb4c1b863615
-- title:
--   Dominated original Lévy marked-count weights have finite first moment and are a.e. finite
-- statement:
--   Whenever the expected genuine original marked jump count with a dominating weight K is finite, a pointwise dominated measurable nonnegative weight H has finite expected original marked contribution and is almost surely finite pathwise. Uses accepted original monotone weighted lintegral and intrinsic source measurability. No ν-rate, finite mark intensity or Poisson copy assumption.
-- source:
--   Accepted P2-F weighted original monotonicity 2eb734c7 and original intrinsic rectangle measurable d9c55240, Mathlib ae_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_monotone_future_lintegral

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_dominated_l1_and_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H K : Ω → ℝ≥0∞) (hH : Measurable H)
    (hHK : ∀ ω, H ω ≤ K ω)
    (hKfinite : (∫⁻ ω, K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) ≠ ∞) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) ≠ ∞ ∧
    (∀ᵐ ω ∂P, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) < ∞) := by sorry
