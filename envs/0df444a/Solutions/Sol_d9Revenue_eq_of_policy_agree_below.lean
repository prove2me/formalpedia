-- Prove2me | solution 1 for d9Revenue_eq_of_policy_agree_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:40:52.088596+00:00
-- url     : https://prove2.me/submissions/07d6adbc-7629-4b10-b54d-837f0778a9cd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (f p q x : ℕ → ℝ) :
    ∀ k, (∀ i, 1 ≤ i → i < k → p i = q i) →
      ∀ s, revenue f p x k s = revenue f q x k s := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro hagree s
      simp [revenue]
  | one =>
      intro hagree s
      simp [revenue]
  | more n ih0 ih1 =>
      intro hagree s
      have hcut : p (n + 1) = q (n + 1) :=
        hagree (n + 1) (by omega) (by omega)
      have hprefix : ∀ t, revenue f p x (n + 1) t =
          revenue f q x (n + 1) t := by
        intro t
        exact ih1 (by
          intro i hi hlt
          exact hagree i hi (by omega)) t
      by_cases hprotection : s < p (n + 1)
      · simp [revenue, hprotection, hcut, hprefix]
      · by_cases hcapacity : s < p (n + 1) + x (n + 2)
        · simp [revenue, hprotection, hcapacity, hcut, hprefix]
        · simp [revenue, hprotection, hcapacity, hcut, hprefix]
