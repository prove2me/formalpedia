-- Prove2me | solution 1 for d9RightSlope_abs_le_fare_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:30:27.474403+00:00
-- url     : https://prove2.me/submissions/f919668a-be9e-44ed-89b6-2fc83f725af0

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9RightSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → |f i| ≤ M) →
      ∀ s, |d9RightSlope f p x k s| ≤ M := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro _ s
      simpa [d9RightSlope] using hM
  | one =>
      intro hfare s
      have hf := hfare 1 (by omega) (by omega)
      by_cases hs : s < x 1 <;> simp [d9RightSlope, hs, hf, hM]
  | more n ih0 ih1 =>
      intro hfare s
      have htail : ∀ i, 1 ≤ i → i ≤ n + 1 → |f i| ≤ M := by
        intro i hi1 hi2
        exact hfare i hi1 (by omega)
      by_cases hbelow : s < p (n + 1)
      · simpa [d9RightSlope, hbelow] using ih1 htail s
      · by_cases hmiddle : s < p (n + 1) + x (n + 2)
        · simpa [d9RightSlope, hbelow, hmiddle] using
            hfare (n + 2) (by omega) (by omega)
        · simpa [d9RightSlope, hbelow, hmiddle] using
            ih1 htail (s - x (n + 2))
