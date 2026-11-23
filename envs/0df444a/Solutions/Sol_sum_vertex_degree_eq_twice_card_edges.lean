-- Prove2me | solution 1 for sum_vertex_degree_eq_twice_card_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:52.803814+00:00
-- url     : https://prove2.me/submissions/7b70acf6-6c58-4098-bdc0-f292d310e06d

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_sum_card_filter_eq_mul
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
private lemma edge_endpoints_distinct (G : CFGraph) (e : G.V × G.V) (he : e ∈ G.edges) :
    e.1 ≠ e.2 := by
  by_contra eq_endpoints
  rcases e with ⟨u,v⟩
  have : u = v := eq_endpoints
  rw [this] at he
  exact G.loopless v he
private lemma edge_incident_vertices_count (G : CFGraph) (e : G.V × G.V) (he : e ∈ G.edges) :
    (Finset.univ.filter (λ v => e.1 = v ∨ e.2 = v)).card = 2 := by
  rw [Finset.card_eq_two]
  refine ⟨e.1, e.2, edge_endpoints_distinct G e he, ?_⟩
  ext v
  simp only [eq_comm, Finset.mem_filter, mem_univ, true_and, mem_insert, Finset.mem_singleton]
private lemma degree_eq_total_flow {T : Type*} [DecidableEq T] [Fintype T] :
    ∀ (S : Multiset (T × T)) (v : T), (∀ e ∈ S, e.1 ≠ e.2) →
      ∑ u : T, Multiset.card (Multiset.filter (fun e ↦ e = (v, u) ∨ e = (u, v)) S) =
        Multiset.card (S.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  -- Induct on the multiset S
  intro S v h_loopless
  induction S using Multiset.induction_on with
  | empty =>
    simp only [filter_zero, Multiset.card_zero, sum_const_zero]
  | cons e_head s_tail ih_s_tail =>
    -- Rewrite both sides using the head and tail
    simp only [Multiset.filter_cons, card_add, sum_add_distrib]
    rw [ih_s_tail]
    -- Cancel the like terms in a + b = a + c
    suffices h :
        ∑ x : T, Multiset.card (if e_head = (v, x) ∨ e_head = (x, v) then {e_head} else 0) =
          Multiset.card (if e_head.1 = v ∨ e_head.2 = v then {e_head} else 0) by
      linarith

    rcases e_head with ⟨e, f⟩
    by_cases h_ev : e = v
    · subst h_ev
      have h_ef : e ≠ f := h_loopless (e, f) (by simp only [Multiset.mem_cons, true_or])
      have h_fv : f ≠ e := by simpa only [ne_eq, eq_comm] using h_ef
      rw [Finset.sum_eq_single f]
      · simp only [Prod.mk.injEq, true_or, ↓reduceIte, Multiset.card_singleton]
      · intro x _ h_x
        have h_fx : f ≠ x := fun h => h_x h.symm
        simp only [Prod.mk.injEq, h_fx, and_false, h_fv, or_self, ↓reduceIte, Multiset.card_zero]
      · simp only [mem_univ, not_true_eq_false, Prod.mk.injEq, true_or, ↓reduceIte,
          Multiset.card_singleton, one_ne_zero, imp_self]
    · by_cases h_fv : f = v
      · subst h_fv
        rw [Finset.sum_eq_single e]
        · simp only [Prod.mk.injEq, or_true, ↓reduceIte, Multiset.card_singleton]
        · intro x _ h_x
          have h_ex : e ≠ x := fun h => h_x h.symm
          simp only [Prod.mk.injEq, h_ev, false_and, h_ex, and_true, or_self, ↓reduceIte,
              Multiset.card_zero]
        · simp only [mem_univ, not_true_eq_false, Prod.mk.injEq, or_true, ↓reduceIte,
            Multiset.card_singleton, one_ne_zero, imp_self]
      · simp only [Prod.mk.injEq, h_ev, false_and, h_fv, and_false, or_self, ↓reduceIte,
          Multiset.card_zero, sum_const_zero]
    intro e
    specialize h_loopless e
    intro h_tail
    apply h_loopless
    simp only [Multiset.mem_cons, h_tail, or_true]
private lemma sum_num_edges_eq_filter_count (G : CFGraph) (v : G.V) :
  ∑ u, num_edges G v u = Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v)) := by
  dsimp only [num_edges]
  have h_loopless: ∀ e ∈ G.edges, e.1 ≠ e.2 := by
    intro e he
    exact edge_endpoints_distinct G e he
  exact degree_eq_total_flow G.edges v (h_loopless)
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution (G : CFGraph) :
    ∑ v, vertex_degree G v = 2 * ↑(Multiset.card G.edges) := by
  calc ∑ v, vertex_degree G v
    = ∑ v, ∑ u, (num_edges G v u : ℤ) := by simp_rw [vertex_degree]
    _ = ∑ v, ↑(∑ u, num_edges G v u) := by simp_rw [← Nat.cast_sum]
    _ = ∑ v, ↑(Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) := by simp_rw [sum_num_edges_eq_filter_count G]
    _ = ↑(∑ v, Multiset.card (G.edges.filter (λ e => e.fst = v ∨ e.snd = v))) := by rw [← Nat.cast_sum]
    _ = ↑(2 * Multiset.card G.edges) := by
      -- Each edge is incident to exactly two vertices
      rw [sum_card_filter_eq_mul G G.edges (λ v e => e.fst = v ∨ e.snd = v) 2
        (edge_incident_vertices_count G)]
    _ = 2 * ↑(Multiset.card G.edges) := by rw [Nat.cast_mul, Nat.cast_two]
