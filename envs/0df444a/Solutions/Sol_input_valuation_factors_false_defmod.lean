-- Prove2me | solution 1 for input_valuation_factors_false_defmod
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-13T08:09:04.839108+00:00
-- url     : https://prove2.me/submissions/71d41ce7-68e2-4600-8ab3-8b7dbe8acb46

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_syracuseValuation

attribute [instance] Classical.propDecidable

theorem solution :
    ¬ ∀ n₀ n m : ℕ, Odd n → valSum n₀ n ≤ m →
      valVec n₀ n = valVec n₀ (n % 2 ^ m) := by
  have f10 : Nat.factorization 10 2 = 1 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 : ℕ) ∣ 5 by norm_num)]
  have f4 : Nat.factorization 4 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow_self Nat.prime_two]
  intro h
  have hsum : valSum 1 3 ≤ 1 := by
    have hval : valSum 1 3 = Nat.factorization 10 2 := by
      unfold valSum
      rw [Fin.sum_univ_one _]
      rfl
    rw [hval, f10]
  have hcon := h 1 3 1 ⟨1, rfl⟩ hsum
  have h0 : valVec 1 3 (⟨0, Nat.one_pos⟩ : Fin 1) =
      valVec 1 (3 % 2 ^ 1) (⟨0, Nat.one_pos⟩ : Fin 1) :=
    congrFun hcon _
  have e1 : valVec 1 3 (⟨0, Nat.one_pos⟩ : Fin 1) = Nat.factorization 10 2 := rfl
  have e2 : valVec 1 (3 % 2 ^ 1) (⟨0, Nat.one_pos⟩ : Fin 1) =
      Nat.factorization 4 2 := rfl
  rw [e1, e2, f10, f4] at h0
  norm_num at h0
