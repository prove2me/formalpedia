-- Prove2me | solution 2 for davenport_constant_groups
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:28:33.703121+00:00
-- url     : https://prove2.me/submissions/b3fd5012-2f1b-49e5-a207-14cc6584738d

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Tauto

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ (D : ℕ), D = 2 * n - 1 ∧
    ∀ (seq : Fin D → ZMod n),
      ∃ (I : Finset (Fin D)) (_ : I.Nonempty),
        (I.sum seq) = 0 := by
  refine ⟨2 * n - 1, rfl, ?_⟩
  intro seq
  haveI : NeZero n := ⟨by omega⟩
  -- Prefix sums `S j = seq 0 + ⋯ + seq (j-1)` for `j = 0, …, n`: `n + 1` values in `ZMod n`.
  let S : Fin (n + 1) → ZMod n := fun j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * n - 1) => i.val < j.val), seq i
  have hcard : Fintype.card (ZMod n) < Fintype.card (Fin (n + 1)) := by
    rw [ZMod.card, Fintype.card_fin]; omega
  obtain ⟨j, k, hjk, hS⟩ := Fintype.exists_ne_map_eq_of_card_lt S hcard
  -- Two equal prefix sums `S j = S k` with `j < k` give the zero-sum block `[j, k)`.
  have key : ∀ j k : Fin (n + 1), j < k → S j = S k →
      ∃ (I : Finset (Fin (2 * n - 1))) (_ : I.Nonempty), I.sum seq = 0 := by
    intro j k hlt hS
    have hlt' : j.val < k.val := hlt
    have hk : k.val ≤ n := Nat.lt_succ_iff.mp k.isLt
    refine ⟨Finset.univ.filter (fun i : Fin (2 * n - 1) => j.val ≤ i.val ∧ i.val < k.val), ?_, ?_⟩
    · refine ⟨⟨j.val, by omega⟩, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_refl _, hlt'⟩
    · have hsplit := Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun i : Fin (2 * n - 1) => i.val < k.val))
        (fun i : Fin (2 * n - 1) => i.val < j.val) seq
      have e1 : (Finset.univ.filter (fun i : Fin (2 * n - 1) => i.val < k.val)).filter
          (fun i => i.val < j.val) =
          Finset.univ.filter (fun i : Fin (2 * n - 1) => i.val < j.val) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨by omega, h⟩
      have e2 : (Finset.univ.filter (fun i : Fin (2 * n - 1) => i.val < k.val)).filter
          (fun i => ¬ i.val < j.val) =
          Finset.univ.filter (fun i : Fin (2 * n - 1) => j.val ≤ i.val ∧ i.val < k.val) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        tauto
      rw [e1, e2] at hsplit
      have hsum : S j + (Finset.univ.filter
          (fun i : Fin (2 * n - 1) => j.val ≤ i.val ∧ i.val < k.val)).sum seq = S k := hsplit
      rw [hS] at hsum
      linear_combination hsum
  rcases lt_or_gt_of_ne hjk with h | h
  · exact key j k h hS
  · exact key k j h hS.symm
