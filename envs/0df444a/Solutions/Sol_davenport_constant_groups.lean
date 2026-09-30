-- Prove2me | solution 1 for davenport_constant_groups
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T01:16:44.411858+00:00
-- url     : https://prove2.me/submissions/a1dcbbf4-d985-453a-8ff5-3265453aab30

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ (D : ℕ), D = 2 * n - 1 ∧
    ∀ (seq : Fin D → ZMod n),
      ∃ (I : Finset (Fin D)) (_ : I.Nonempty),
        (I.sum seq) = 0 := by
  classical
  let : NeZero n := ⟨by omega⟩
  refine ⟨2 * n - 1, rfl, ?_⟩
  intro seq
  let pref (j : Fin (n + 1)) : Finset (Fin (2 * n - 1)) :=
    Finset.univ.filter (fun i => i.val < j.val)
  let sums (j : Fin (n + 1)) : ZMod n := ∑ i ∈ pref j, seq i
  have hnot : ¬ Function.Injective sums := by
    intro hinj
    have hcard := Fintype.card_le_of_injective sums hinj
    simp only [Fintype.card_fin, ZMod.card] at hcard
    omega
  change ¬ ∀ i j, sums i = sums j → i = j at hnot
  push Not at hnot
  obtain ⟨i, j, heq, hne⟩ := hnot
  have build (a b : Fin (n + 1)) (hlt : a < b) (hab : sums a = sums b) :
      ∃ (I : Finset (Fin (2 * n - 1))) (_ : I.Nonempty), I.sum seq = 0 := by
    have hsub : pref a ⊆ pref b := by
      intro x hx
      simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx.trans hlt
    let I := pref b \ pref a
    have hane : a.val < 2 * n - 1 := by have := b.isLt; omega
    have hmem : (⟨a.val, hane⟩ : Fin (2 * n - 1)) ∈ I := by
      simp [I, pref, hlt]
    refine ⟨I, ⟨_, hmem⟩, ?_⟩
    have hsum := Finset.sum_sdiff hsub (f := seq)
    change (∑ x ∈ I, seq x) + sums a = sums b at hsum
    rw [hab] at hsum
    exact add_right_cancel (hsum.trans (zero_add (sums b)).symm)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact build i j hlt heq
  · exact build j i hlt heq.symm

#print axioms solution
