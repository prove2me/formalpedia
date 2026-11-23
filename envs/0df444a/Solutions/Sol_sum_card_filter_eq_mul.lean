-- Prove2me | solution 1 for sum_card_filter_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:43:46.599317+00:00
-- url     : https://prove2.me/submissions/25daf2a2-854b-43ae-9c68-dab434ad42fa

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
private lemma sum_filter_eq_map (G : CFGraph) (M : Multiset (G.V × G.V)) (crit  : G.V → G.V × G.V → Prop)
    [∀ v e, Decidable (crit v e)] :
  ∑ v : G.V, Multiset.card (M.filter (crit v))
    = Multiset.sum (M.map (λ e => (Finset.univ.filter (λ v => (crit v e) )).card)) := by
  -- Define P and g using Prop for clarity in the proof - Available throughout
  let P : G.V → G.V × G.V → Prop := fun v e => crit v e
  let g : G.V × G.V → ℕ := fun e => (Finset.univ.filter (P · e)).card

  -- Rewrite the goal using P and g for proof readability
  suffices goal_rewritten : ∑ v : G.V, Multiset.card (M.filter (P v)) = Multiset.sum (M.map g) by
    exact goal_rewritten -- The goal is now exactly the statement `goal_rewritten`

  -- Prove the rewritten goal by induction on the multiset G.edges
  induction M using Multiset.induction_on with
  | empty =>
    simp only [filter_zero, Multiset.card_zero, sum_const_zero, Multiset.map_zero,
        sum_zero] -- Use _zero lemmas
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite RHS: sum(map(g, e_head::s_tail)) = g e_head + sum(map(g, s_tail))
    rw [Multiset.map_cons, Multiset.sum_cons]

    -- Rewrite LHS: ∑ v, card(filter(P v, e_head::s_tail))
    simp_rw [← Multiset.countP_eq_card_filter]
    simp only [countP_cons]
    rw [Finset.sum_add_distrib]

    -- Simplify the second sum (∑ v, ite (P v e_head) 1 0) to g e_head
    have h_sum_ite_eq_card : ∑ v : G.V, ite (P v e_head) 1 0 = g e_head := by
      rw [← Finset.card_filter] -- This completes the proof for h_sum_ite_eq_card
    rw [h_sum_ite_eq_card]

    simp_rw [Multiset.countP_eq_card_filter]
    rw [add_comm, ih_s_tail]
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution (G : CFGraph) (M : Multiset (G.V × G.V))
    (crit : G.V → G.V × G.V → Prop) [∀ v e, Decidable (crit v e)] (c : ℕ)
    (h_count : ∀ e ∈ M, (Finset.univ.filter (λ v => crit v e)).card = c) :
  ∑ v : G.V, Multiset.card (M.filter (crit v)) = c * Multiset.card M := by
  rw [sum_filter_eq_map G M crit, Multiset.map_congr rfl h_count, Multiset.map_const',
    Multiset.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_comm]
