-- Prove2me | solution 1 for mme_finset_pointwise_one_eighth_aggregate_nonholes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:24:12.801964+00:00
-- url     : https://prove2.me/submissions/253108de-0add-4c42-91f7-2f6e7411baf1

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Weight Block : Type}
    [Fintype Weight] [Fintype Block]
    [DecidableEq Weight] [DecidableEq Block]
    (bad : Block → Weight → Prop) [DecidableRel bad]
    (hpointwise : ∀ z : Block,
      8 * (Finset.univ.filter (bad z)).card ≤ Fintype.card Weight) :
    7 * Fintype.card Weight * Fintype.card Block ≤
      8 * ∑ w : Weight,
        (Finset.univ.filter (fun z : Block ↦ ¬ bad z w)).card := by
  let holes : Weight → ℕ := fun w ↦
    (Finset.univ.filter (fun z : Block ↦ bad z w)).card
  let nonholes : Weight → ℕ := fun w ↦
    (Finset.univ.filter (fun z : Block ↦ ¬ bad z w)).card
  let total : ℕ := Fintype.card Weight * Fintype.card Block
  have hpartition (w : Weight) :
      holes w + nonholes w = Fintype.card Block := by
    dsimp only [holes, nonholes]
    simpa only [Finset.card_univ] using
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Block)) (p := fun z ↦ bad z w)
  have hdouble :
      (∑ w : Weight, holes w) =
        ∑ z : Block, (Finset.univ.filter (bad z)).card := by
    dsimp only [holes]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hholes : 8 * (∑ w : Weight, holes w) ≤ total := by
    rw [hdouble, Finset.mul_sum]
    calc
      ∑ z : Block, 8 * (Finset.univ.filter (bad z)).card ≤
          ∑ _z : Block, Fintype.card Weight :=
        Finset.sum_le_sum fun z _ ↦ hpointwise z
      _ = total := by simp [total, mul_comm]
  have htotal :
      (∑ w : Weight, holes w) + (∑ w : Weight, nonholes w) =
        total := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hpartition]
    simp [total]
  have hresult :
      7 * total ≤ 8 * ∑ w : Weight, nonholes w := by
    omega
  simpa only [total, nonholes, Nat.mul_assoc] using hresult
