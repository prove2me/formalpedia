-- Prove2me | solution 1 for revenue_update_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:11:17.898044+00:00
-- url     : https://prove2.me/submissions/12adee30-25cd-4082-8504-e37b9619ca7e

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (f p x : ℕ → ℝ) :
    ∀ (n i : ℕ), n < i → ∀ (y s : ℝ),
      revenue f p (Function.update x i y) n s = revenue f p x n s := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro i hi y s
      simp [revenue]
  | one =>
      intro i hi y s
      have hne : 1 ≠ i := ne_of_lt hi
      simp [revenue, Function.update_of_ne hne]
  | more n ih0 ih1 =>
      intro i hi y s
      have hne : n + 2 ≠ i := ne_of_lt (by omega)
      have htail : n + 1 < i := by omega
      simp only [revenue, Function.update_of_ne hne]
      rw [ih1 i htail y s, ih1 i htail y (p (n + 1)),
        ih1 i htail y (s - x (n + 2))]
