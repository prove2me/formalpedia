-- Prove2me | solution 1 for input_valuation_factors
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-21T17:14:49.063233+00:00
-- url     : https://prove2.me/submissions/785253c7-0fbf-4c7b-aa6c-46d187996f93

import Mathlib
import Definitions.Def_syracuseOrbitMin
set_option autoImplicit false

noncomputable section

attribute [instance] Classical.propDecidable

theorem solution :
    ¬ ∀ n₀ n m : ℕ, Odd n → (Finset.sum Finset.univ (fun j : Fin n₀ => Nat.factorization (3 * (syracuseStep^[j.val] n) + 1) 2)) ≤ m →
      (fun j : Fin n₀ => Nat.factorization (3 * (syracuseStep^[j.val] n) + 1) 2) = (fun j : Fin n₀ => Nat.factorization (3 * (syracuseStep^[j.val] (n % 2 ^ m)) + 1) 2) := by
  intro h
  have hf4 : Nat.factorization 4 2 = 2 := by
    have : (4:ℕ) = 2 ^ 2 := by norm_num
    rw [this, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hf10 : Nat.factorization 10 2 = 1 := by
    have h5 : Nat.factorization 5 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    have h2 : Nat.factorization 2 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
    rw [show (10:ℕ) = 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [h5, h2]
  have h1 := h 1 3 1 (by decide) (by simp [hf10])
  have := congrFun h1 0
  simp at this
  norm_num at this
  rw [hf4, hf10] at this
  omega
