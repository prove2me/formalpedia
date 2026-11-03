-- Prove2me | solution 1 for levy_foundations_thinnedCountToENNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:36:55.517997+00:00
-- url     : https://prove2.me/submissions/bbec1145-5036-4b21-82cc-993642b5e89f

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_thinnedCount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω E : Type*} (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (A : Set E)
    (k : ℕ) (ω : Ω) :
    (LevyFoundations.thinnedCount K X A k ω : ℝ≥0∞) =
      ∑ n ∈ Finset.range (K k ω),
        A.indicator (1 : E → ℝ≥0∞) (X k n ω) := by
  classical
  rw [LevyFoundations.thinnedCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : X k n ω ∈ A
  · rw [Set.indicator_of_mem hx, if_pos hx, Pi.one_apply, Nat.cast_one]
  · rw [Set.indicator_of_notMem hx, if_neg hx, Nat.cast_zero]
