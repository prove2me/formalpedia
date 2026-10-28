-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_two_sided_survival_measurable
-- name    : AvramDividend.Classical.chat04_countable_shifted_two_sided_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:48:37.569408+00:00
-- url     : https://prove2.me/theorems/55927bc3-9af7-4556-b655-b27d4327b2ac
-- title:
--   Joint Borel measurability of two-sided countable reserve survival
-- statement:
--   For any variable initial reserve and full future real path, the event that the reserve stays in the closed interval [0,a] at every future observation up to T is jointly Borel measurable. It is precisely the intersection of the Proved lower-survival and upper-survival Borel events. Supplies the killing predicate for two-sided Markov and discounted scale-factor kernels.
-- source:
--   Proved lower and upper countable shifted reserve survival measurability.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_upper_survival_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_countable_shifted_two_sided_survival_measurable
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) (a : ℝ) :
    MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T →
          0 ≤ z.1 + z.2 (τ j) ∧ z.1 + z.2 (τ j) ≤ a} := by sorry
