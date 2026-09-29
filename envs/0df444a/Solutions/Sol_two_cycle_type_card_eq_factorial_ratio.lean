-- Prove2me | solution 1 for two_cycle_type_card_eq_factorial_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T03:17:16.020383+00:00
-- url     : https://prove2.me/submissions/702544c5-1458-40fa-81c6-e1ab03c6392b

import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

theorem solution (n : Nat) :
    (({g | g.cycleType = Multiset.replicate n 2} :
        Finset (Equiv.Perm (Fin (2 * n)))).card : ℝ) =
      (Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)) := by
  classical
  let m : Multiset Nat := Multiset.replicate n 2
  let cardSet : Nat :=
    ({g | g.cycleType = m} : Finset (Equiv.Perm (Fin (2 * n)))).card
  let denNat : Nat := (2 ^ n) * Nat.factorial n
  have hsum : m.sum = 2 * n := by
    simp [m, Multiset.sum_replicate]
    omega
  have hprodM : m.prod = 2 ^ n := by
    simp [m, Multiset.prod_replicate]
  have hprod :
      (∏ x ∈ m.toFinset, (Multiset.count x m).factorial) = Nat.factorial n := by
    by_cases hn0 : n = 0
    · subst n
      simp [m]
    · simp [m, Multiset.toFinset_replicate, hn0, Multiset.count_replicate_self]
  have hcond : m.sum ≤ Fintype.card (Fin (2 * n)) ∧ ∀ a ∈ m, 2 ≤ a := by
    constructor
    · simp [hsum, Fintype.card_fin]
    · intro a ha
      rw [show m = Multiset.replicate n 2 by rfl, Multiset.mem_replicate] at ha
      exact ha.2 ▸ le_rfl
  have hmul0 := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2 * n)) m
  have hmul : cardSet * denNat = Nat.factorial (2 * n) := by
    rw [if_pos hcond] at hmul0
    simpa [cardSet, denNat, Fintype.card_fin, hsum, hprodM, hprod,
      Nat.sub_self, Nat.factorial_zero, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hmul0
  have hden_pos_nat : 0 < denNat := by
    dsimp [denNat]
    positivity
  have hden_ne : (denNat : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hden_pos_nat)
  have hmulR : (cardSet : ℝ) * (denNat : ℝ) = (Nat.factorial (2 * n) : ℝ) := by
    exact_mod_cast hmul
  have hcard : (cardSet : ℝ) = (Nat.factorial (2 * n) : ℝ) / (denNat : ℝ) := by
    exact (eq_div_iff hden_ne).2 hmulR
  simpa [m, cardSet, denNat] using hcard
