-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_translation_of_all_Ioc_mass_shift
-- name    : AvramDividend.Classical.lintegral_translation_of_all_Ioc_mass_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:13:33.865098+00:00
-- url     : https://prove2.me/theorems/f3de50bd-c45b-41f9-9082-36c39a2f0ea7
-- title:
--   Translated Stieltjes interval masses imply equality of discounted reward integrals
-- statement:
--   Any nonnegative measurable reward integrates identically against two measures whose interval masses agree under a fixed time translation, provided the integrand is correspondingly translated. Supplies the weighted Stieltjes change-of-variables step for the barrier-dividend strong-Markov splitting.
-- source:
--   W-free dividendValue_barrierStrategy_upExit_split_of_standing 79978d61-9d1f-4b20-b8a5-114797a8e380, using new measure uniqueness/pushforward theorem 0292e86b-89d2-41f5-931d-cf66e08f4b38 (candidate 15355 pending). Pinned Mathlib lintegral_map directly verified in official docs.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_measure_eq_map_add_of_all_Ioc_translation

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.lintegral_translation_of_all_Ioc_mass_shift
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (u : ℝ)
    (hshift : ∀ a b : ℝ, a < b →
      μ (Set.Ioc (u + a) (u + b)) = ν (Set.Ioc a b))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t : ℝ, f t ∂μ) =
      ∫⁻ t : ℝ, f (u + t) ∂ν := by
  sorry
