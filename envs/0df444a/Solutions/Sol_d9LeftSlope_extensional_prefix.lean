-- Prove2me | solution 1 for d9LeftSlope_extensional_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:10:33.586717+00:00
-- url     : https://prove2.me/submissions/e669d001-59c9-4c0b-93a5-f4f9d47aef79

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9LeftSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (f p : ℕ → ℝ) (x y : ℕ → ℝ) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → x i = y i) →
      ∀ s, d9LeftSlope f p x k s = d9LeftSlope f p y k s := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro _ s
      rfl
  | one =>
      intro hxy s
      simp [d9LeftSlope, hxy 1 (by omega) (by omega)]
  | more n ih0 ih1 =>
      intro hxy s
      have hnext : x (n + 2) = y (n + 2) :=
        hxy (n + 2) (by omega) (by omega)
      have htail : ∀ i, 1 ≤ i → i ≤ n + 1 → x i = y i := by
        intro i hi1 hi2
        exact hxy i hi1 (by omega)
      have ih := ih1 htail
      simp only [d9LeftSlope, hnext]
      by_cases hbelow : s ≤ p (n + 1)
      · simp [hbelow, ih]
      · by_cases hmiddle : s ≤ p (n + 1) + x (n + 2)
        · rw [hnext] at hmiddle
          simp [hbelow, hmiddle]
        · rw [hnext] at hmiddle
          simp [hbelow, hmiddle, ih]
