-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_upper_survival_measurable
-- name    : AvramDividend.Classical.chat04_countable_shifted_future_reserve_upper_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:42:01.453888+00:00
-- url     : https://prove2.me/theorems/43d47dd6-3ac5-4a78-a184-e4fd2f886d72
-- title:
--   Borel measurability of countably monitored shifted reserve below any upper barrier
-- statement:
--   The event that the sum of a variable current reserve and an arbitrary future path stays at or below a real upper barrier at every scheduled time not exceeding a deterministic horizon is jointly Borel measurable in reserve and path, for every countable schedule. This is the upper counterpart to the Proved countable nonnegative-survival measurable set, used in two-sided killed Markov kernels.
-- source:
--   Pinned Mathlib measurable_fst, measurable_pi_apply, measurableSet_le, and measurableSet_iInter, dual to the Proved lower-survival lemma.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_countable_shifted_future_reserve_upper_survival_measurable
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) (a : ℝ) :
    MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → z.1 + z.2 (τ j) ≤ a} := by sorry
