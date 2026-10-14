-- Prove2me | solution 1 for input_valuation_equidistribution_false_defmod
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-13T08:09:09.682975+00:00
-- url     : https://prove2.me/submissions/d74ae939-b148-4be2-8b2a-b5bf47cdc6de

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_syracuseValuation

attribute [instance] Classical.propDecidable

/-- `syrVal 0 = 0` since `3 * 0 + 1 = 1` is not divisible by `2`. -/
private lemma syrVal_zero : syrVal 0 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by norm_num)

/-- `syrVal 1 = 2` since `3 * 1 + 1 = 4 = 2 ^ 2`. -/
private lemma syrVal_one : syrVal 1 = 2 := by
  show Nat.factorization (2 ^ 2) 2 = 2
  exact Nat.factorization_pow_self Nat.prime_two

/-- `syrVal 2 = 0` since `3 * 2 + 1 = 7` is not divisible by `2`. -/
private lemma syrVal_two : syrVal 2 = 0 := by
  show Nat.factorization 7 2 = 0
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num)

/-- `syrVal 3 = 1` since `3 * 3 + 1 = 10 = 2 * 5` with `2 ∤ 5`. -/
private lemma syrVal_three : syrVal 3 = 1 := by
  show Nat.factorization (2 * 5) 2 = 1
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 5 by norm_num)]

/-- A length-one valuation vector records the valuation at the starting point. -/
private lemma valVec_one_apply (r : ℕ) :
    valVec 1 r (⟨0, zero_lt_one⟩ : Fin 1) = syrVal r := rfl

/-- Among residues below `4`, only `3` is odd with valuation vector `(1,)`. -/
private lemma card_filter_valVec_one :
    (Finset.filter (fun r => Odd r ∧ valVec 1 r = (fun _ => 1))
      (Finset.range (2 ^ 2))).card = 1 := by
  have h4 : (2 : ℕ) ^ 2 = 4 := rfl
  rw [h4]
  have hset : Finset.filter (fun r => Odd r ∧ valVec 1 r = (fun _ => 1))
      (Finset.range 4) = {3} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hr4, hodd, hvec_eq⟩
      interval_cases r
      · norm_num at hodd
      · have h0 := congrFun hvec_eq (⟨0, zero_lt_one⟩ : Fin 1)
        rw [valVec_one_apply] at h0
        have h1 : syrVal 1 = 1 := h0
        rw [syrVal_one] at h1
        norm_num at h1
      · norm_num at hodd
      · rfl
    · intro hr
      subst hr
      refine ⟨by norm_num, by norm_num, ?_⟩
      funext j
      have hj0 : j = (⟨0, zero_lt_one⟩ : Fin 1) := Subsingleton.elim _ _
      subst hj0
      exact syrVal_three
  rw [hset, Finset.card_singleton]

theorem solution :
    ¬ ∀ n₀ m : ℕ, 1 ≤ n₀ → ∀ ā : Fin n₀ → ℕ, (∀ j, 1 ≤ ā j) →
      Finset.sum Finset.univ (fun j => ā j) ≤ m →
      (Finset.filter (fun r => Odd r ∧ valVec n₀ r = ā) (Finset.range (2 ^ m))).card
        = 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by
  intro h
  have h2 := h 1 2 le_rfl (fun _ => 1) (fun _ => le_rfl) (by decide)
  have hval : 2 ^ (2 - Finset.sum Finset.univ (fun _ : Fin 1 => (1 : ℕ))) = 2 := by
    decide
  exact (by norm_num : (1 : ℕ) ≠ 2)
    (card_filter_valVec_one.symm.trans (h2.trans hval))
