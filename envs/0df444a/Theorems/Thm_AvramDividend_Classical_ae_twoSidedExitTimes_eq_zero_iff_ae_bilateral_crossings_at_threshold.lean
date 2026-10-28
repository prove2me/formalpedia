-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_twoSidedExitTimes_eq_zero_iff_ae_bilateral_crossings_at_threshold
-- name    : AvramDividend.Classical.ae_twoSidedExitTimes_eq_zero_iff_ae_bilateral_crossings_at_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:10:02.83577+00:00
-- url     : https://prove2.me/theorems/efa38e90-ef6d-4653-ada7-b5a610d6d536
-- title:
--   Almost-sure bilateral regularity at an arbitrary threshold
-- statement:
--   Almost-sure instantaneous first passage on both sides is equivalent to almost-sure arbitrarily early path visits on both sides of any real threshold.
-- source:
--   Pointwise accepted first-passage equivalences, transported through almost-everywhere implications.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_twoSidedExitTimes_eq_zero_iff_ae_bilateral_crossings_at_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    (∀ᵐ ω ∂P,
      twoSidedExitDownTime X b ω = 0 ∧ twoSidedExitUpTime X b ω = 0) ↔
      (∀ᵐ ω ∂P,
        (∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) ∧
        (∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω)) := by sorry
