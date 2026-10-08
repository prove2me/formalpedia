-- Prove2me | solution 1 for d9_finite_fare_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:47:05.464043+00:00
-- url     : https://prove2.me/submissions/a1ee0043-31f5-4201-8843-b61f781f5869

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution (f : ℕ → ℝ) :
    ∀ k, ∃ M, 0 ≤ M ∧ ∀ i, 1 ≤ i → i ≤ k → |f i| ≤ M := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro i hi hik
      omega
  | one =>
      refine ⟨|f 1|, abs_nonneg _, ?_⟩
      intro i hi hik
      have hidx : i = 1 := by omega
      subst i
      exact le_rfl
  | more n ih0 ih1 =>
      obtain ⟨M, hM, hbound⟩ := ih1
      refine ⟨max M |f (n + 2)|,
        le_trans hM (le_max_left _ _), ?_⟩
      intro i hi hik
      rcases (show i ≤ n + 1 ∨ i = n + 2 by omega) with hleft | heq
      · exact (hbound i hi (by omega)).trans (le_max_left _ _)
      · subst i
        exact le_max_right _ _
