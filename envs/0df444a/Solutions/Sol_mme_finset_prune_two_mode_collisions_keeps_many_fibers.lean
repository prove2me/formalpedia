-- Prove2me | solution 1 for mme_finset_prune_two_mode_collisions_keeps_many_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:48:32.239876+00:00
-- url     : https://prove2.me/submissions/9cb42e3e-c483-4a36-a0c3-0465a892ef42

import Mathlib
import Theorems.Thm_mme_finset_prune_two_mode_collisions_isolated

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Quantitative fiber retention under two-mode collision pruning. -/
theorem solution
    {α β γ ζ : Type}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq ζ]
    (E : Finset α) (x : α → β) (y : α → γ) (z : α → ζ)
    (Good : Finset ζ) (K H : ℕ)
    (hHK : H ≤ K)
    (hdegree : ∀ c ∈ Good, K ≤ (E.filter (fun e => z e = c)).card) :
    ∃ I : Finset α,
      I ⊆ E ∧
      (∀ e ∈ I, ∀ e' ∈ E,
        x e = x e' ∨ y e = y e' → e = e') ∧
      (K - H + 1) *
          (Good.filter (fun c => ¬ H ≤
            (I.filter (fun e => z e = c)).card)).card ≤
        ((E.product E).filter (fun p =>
          p.1 ≠ p.2 ∧
            (x p.1 = x p.2 ∨ y p.1 = y p.2))).card := by
  classical
  obtain ⟨I, hIE, hisolated, hprune⟩ :=
    mme_finset_prune_two_mode_collisions_isolated E x y
  let Bad : Finset ζ := Good.filter (fun c => ¬ H ≤
    (I.filter (fun e => z e = c)).card)
  let D : Finset α := E \ I
  have hfiberLoss : ∀ c ∈ Bad,
      K - H + 1 ≤ (D.filter (fun e => z e = c)).card := by
    intro c hc
    have hcGood : c ∈ Good := (Finset.mem_filter.mp hc).1
    have hcBad : ¬ H ≤ (I.filter (fun e => z e = c)).card :=
      (Finset.mem_filter.mp hc).2
    have hIfiber : (I.filter (fun e => z e = c)) ⊆
        (E.filter (fun e => z e = c)) := by
      intro e he
      exact Finset.mem_filter.mpr
        ⟨hIE (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
    have hsplit := Finset.card_sdiff_add_card_eq_card hIfiber
    have hsdiff :
        (E.filter (fun e => z e = c)) \ (I.filter (fun e => z e = c)) =
          D.filter (fun e => z e = c) := by
      ext e
      constructor
      · intro he
        have he' := Finset.mem_sdiff.mp he
        have heE := Finset.mem_filter.mp he'.1
        have heI : e ∉ I := by
          intro hei
          exact he'.2 (Finset.mem_filter.mpr ⟨hei, heE.2⟩)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨heE.1, heI⟩, heE.2⟩
      · intro he
        have he' := Finset.mem_filter.mp he
        have heD := Finset.mem_sdiff.mp he'.1
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨heD.1, he'.2⟩, by
            intro hei
            exact heD.2 (Finset.mem_filter.mp hei).1⟩
    rw [hsdiff] at hsplit
    have hE := hdegree c hcGood
    omega
  have hsumLower :
      (K - H + 1) * Bad.card ≤
        ∑ c ∈ Bad, (D.filter (fun e => z e = c)).card := by
    calc
      (K - H + 1) * Bad.card = ∑ _c ∈ Bad, (K - H + 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ Bad, (D.filter (fun e => z e = c)).card := by
        exact Finset.sum_le_sum hfiberLoss
  have hsumFibers :
      (∑ c ∈ Bad, (D.filter (fun e => z e = c)).card) ≤ D.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hDcollision : D.card ≤
      ((E.product E).filter (fun p =>
        p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card := by
    have hsplit := Finset.card_sdiff_add_card_eq_card hIE
    change D.card + I.card = E.card at hsplit
    omega
  refine ⟨I, hIE, hisolated, ?_⟩
  change (K - H + 1) * Bad.card ≤ _
  exact hsumLower.trans (hsumFibers.trans hDcollision)
