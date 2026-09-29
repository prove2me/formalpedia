-- Prove2me | solution 1 for mme_finite_fiber_threshold_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:58:01.255696+00:00
-- url     : https://prove2.me/submissions/14e4e80d-63ea-4dec-add2-e44bdce7501e

import Mathlib.Tactic
import Mathlib.Data.Finset.Card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (A H Q : ℕ) (hH : 0 < H) (hQ : 0 < Q)
    (t : Fin A → ℕ) (ht : ∀ a, t a ≤ H)
    (hmass : A * H ≤ Q * ∑ a, t a) :
    ∃ H' : ℕ, ∃ S : Finset (Fin A),
      0 < H' ∧
      (∀ a ∈ S, H' ≤ t a) ∧
      A ≤ 2 * Q * S.card ∧
      H ≤ 4 * Q * H' := by
  classical
  by_cases hsmall : H < 2 * Q
  · let S : Finset (Fin A) := Finset.univ.filter (fun a => 0 < t a)
    have hsumUpper : (∑ a, t a) ≤ H * S.card := by
      calc
        (∑ a, t a) ≤
            ∑ a : Fin A, if 0 < t a then H else 0 := by
          apply Finset.sum_le_sum
          intro a _ha
          split_ifs with ha
          · exact ht a
          · omega
        _ = H * S.card := by
          rw [← Finset.sum_filter]
          simp [S, mul_comm]
    have hcancel : A * H ≤ (Q * S.card) * H := by
      calc
        A * H ≤ Q * ∑ a, t a := hmass
        _ ≤ Q * (H * S.card) := Nat.mul_le_mul_left Q hsumUpper
        _ = (Q * S.card) * H := by ring
    have hA : A ≤ Q * S.card :=
      Nat.le_of_mul_le_mul_right hcancel hH
    refine ⟨1, S, by omega, ?_, ?_, ?_⟩
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
    · exact hA.trans (by
        apply Nat.mul_le_mul_right S.card
        omega)
    · omega
  · let h : ℕ := H / (2 * Q)
    have hd : 0 < 2 * Q := by positivity
    have hdenom : 2 * Q ≤ H := by omega
    have hh : 0 < h := by
      exact Nat.div_pos hdenom hd
    let S : Finset (Fin A) := Finset.univ.filter (fun a => h ≤ t a)
    have hsumUpper : (∑ a, t a) ≤ S.card * H + A * h := by
      calc
        (∑ a, t a) ≤
            ∑ a : Fin A, if h ≤ t a then H else h := by
          apply Finset.sum_le_sum
          intro a _ha
          split_ifs with ha
          · exact ht a
          · omega
        _ ≤ ∑ a : Fin A, ((if h ≤ t a then H else 0) + h) := by
          apply Finset.sum_le_sum
          intro a _ha
          split_ifs <;> omega
        _ = S.card * H + A * h := by
          rw [Finset.sum_add_distrib]
          rw [← Finset.sum_filter]
          simp [S, mul_comm]
    have hmain : A * H ≤ Q * (S.card * H + A * h) :=
      hmass.trans (Nat.mul_le_mul_left Q hsumUpper)
    have hdiv : (2 * Q) * h ≤ H := by
      simpa only [h] using Nat.mul_div_le H (2 * Q)
    have hhalf : 2 * (Q * (A * h)) ≤ A * H := by
      calc
        2 * (Q * (A * h)) = A * ((2 * Q) * h) := by ring
        _ ≤ A * H := Nat.mul_le_mul_left A hdiv
    have htwice : A * H ≤ 2 * (Q * (S.card * H)) := by
      have hmain' :
          A * H ≤ Q * (S.card * H) + Q * (A * h) := by
        simpa [Nat.mul_add] using hmain
      omega
    have hA : A ≤ (2 * Q * S.card) := by
      apply Nat.le_of_mul_le_mul_right (c := H) _ hH
      calc
        A * H ≤ 2 * (Q * (S.card * H)) := htwice
        _ = (2 * Q * S.card) * H := by ring
    have hlt : H < (2 * Q) * (h + 1) := by
      simpa only [h] using Nat.lt_mul_div_succ H hd
    have hHbound : H ≤ 4 * Q * h := by
      have hbase : 2 * Q ≤ (2 * Q) * h := by
        simpa using Nat.mul_le_mul_left (2 * Q) hh
      have hlt' : H < 4 * Q * h := by
        calc
          H < (2 * Q) * (h + 1) := hlt
          _ = (2 * Q) * h + 2 * Q := by ring
          _ ≤ (2 * Q) * h + (2 * Q) * h :=
            Nat.add_le_add_left hbase ((2 * Q) * h)
          _ = 4 * Q * h := by ring
      exact hlt'.le
    refine ⟨h, S, hh, ?_, hA, hHbound⟩
    intro a ha
    exact (Finset.mem_filter.mp ha).2
