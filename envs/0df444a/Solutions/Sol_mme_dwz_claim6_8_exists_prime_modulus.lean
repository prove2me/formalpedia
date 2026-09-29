-- Prove2me | solution 1 for mme_dwz_claim6_8_exists_prime_modulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:06:51.503732+00:00
-- url     : https://prove2.me/submissions/8f5429ab-7abe-4a09-8ed5-0bb094fb0b81

import Mathlib.NumberTheory.Bertrand

set_option autoImplicit false
set_option warningAsError true

/-- Proof of the prime-modulus handoff used in DWZ Claim 6.8. -/
theorem solution
    (levelSum firstCollisionBudget compatibleCandidateBudget M0 : ℕ)
    (hM0 : 2 ≤ M0)
    (hlevel : levelSum ≤ M0)
    (hfirst : 8 * firstCollisionBudget ≤ M0)
    (hcompatible : 8 * compatibleCandidateBudget ≤ M0) :
    ∃ p : ℕ,
      p.Prime ∧ Odd p ∧
      levelSum < p ∧
      8 * firstCollisionBudget ≤ p ∧
      8 * compatibleCandidateBudget ≤ p ∧
      M0 < p ∧ p ≤ 2 * M0 := by
  obtain ⟨p, hp, hM0p, hp2M0⟩ :=
    Nat.exists_prime_lt_and_le_two_mul M0 (by omega)
  have hpne2 : p ≠ 2 := by omega
  refine ⟨p, hp, hp.odd_of_ne_two hpne2, ?_, ?_, ?_, hM0p, hp2M0⟩
  · omega
  · omega
  · omega
