-- Prove2me | solution 1 for mme_prime_half_modulus_behrend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:13:11.766276+00:00
-- url     : https://prove2.me/submissions/09b3abdb-7550-435b-b937-b498a21166c6

import Mathlib.NumberTheory.Bertrand
import Theorems.Thm_mme_behrend_explicit_threeAP_free

open Real

set_option autoImplicit false

/-- A Behrend set can be placed in the lower half of a prime modulus while
losing only a factor four between its ambient interval and the modulus. -/
theorem solution (Q : ℕ) (hQ : 0 < Q) :
    ∃ p : ℕ, Nat.Prime p ∧ 2 * Q < p ∧ p ≤ 4 * Q ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) ≤
          (S.card : ℝ) := by
  obtain ⟨p, hp, hp_lower, hp_upper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 * Q) (by omega)
  obtain ⟨S, hS_range, hS_free, hS_card⟩ :=
    mme_behrend_explicit_threeAP_free Q
  refine ⟨p, hp, hp_lower, ?_, S, ?_, hS_free, hS_card⟩
  · omega
  · exact hS_range.trans (Finset.range_mono (by omega))
