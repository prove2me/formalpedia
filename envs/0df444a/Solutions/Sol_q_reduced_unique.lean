-- Prove2me | solution 1 for q_reduced_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:44.856798+00:00
-- url     : https://prove2.me/submissions/db6097a4-ced7-4007-a23d-54ddee6e8f4a

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_principal_iff_eq_prin
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_q_reduced_exists_lt_outdeg
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
private lemma prin_eq_zero_of_two_sided_reducer (G : CFGraph) (q : G.V) (σ : firing_script G)
  (h₁ : q_reducer G q σ) (h₂ : q_reducer G q (-σ)) : prin G σ = 0 := by
  have h_const : ∀ v : G.V, σ v = σ q := by
    intro v
    have hv₂ := h₂ v
    repeat rw [Pi.neg_apply] at hv₂
    linarith [h₁ v]
  rw [show σ = (fun _ : G.V => σ q) from funext h_const, prin_const]
private lemma maxset_of_script (G : CFGraph) (σ : firing_script G) : ∃ S : Finset G.V, S.Nonempty ∧ ∀ v ∈ S, (∀ w : G.V, σ w ≤ σ v ∧ (w ∈ S → σ w = σ v)) ∧ -(prin G σ v) ≥ outdeg_S G S v := by
  let max_exists := Finset.exists_max_image Finset.univ σ
    (by use Classical.arbitrary G.V; simp only [mem_univ])
  rcases max_exists with ⟨w, ⟨_,w_argmax⟩⟩
  let S := Finset.univ.filter (σ · = σ w)
  use S
  constructor
  -- Show S is nonempty
  use w; dsimp only [S]; simp only [Finset.mem_filter, mem_univ, and_self]
  intro x x_in_S
  have h_x : σ x = σ w := by
    dsimp only [S] at x_in_S; simp only [Finset.mem_filter, mem_univ,
        true_and] at x_in_S; exact x_in_S

  constructor
  -- Maximality condition
  intro y
  constructor
  · -- Show σ y ≤ σ x
    specialize w_argmax y (by simp only [mem_univ])
    rw [h_x]; exact w_argmax
  · -- Show that if y ∈ S, then σ y = σ x
    intro y_in_S
    dsimp only [S] at y_in_S; simp only [Finset.mem_filter, mem_univ, true_and] at y_in_S
    rw [h_x]; exact y_in_S
  -- Show the outdegree inequality
  rw [prin_apply]
  rw [outdeg_S_eq_sum_filter]
  simp only [ge_iff_le]
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x ↦ x ∉ S)]

  have : ∑ x_1 ∈ Finset.filter (fun x ↦ ¬x ∉ S) univ, -((σ x_1 - σ x) * ↑(num_edges G x x_1)) = 0 := by
    apply Finset.sum_eq_zero
    intro y h_y
    have h_y : y ∈ S := by simp only [Decidable.not_not, subset_univ,
        filter_mem_eq_of_subset] at h_y; exact h_y
    have h_σy : σ y = σ x := by
      dsimp only [S] at h_y; simp only [Finset.mem_filter, mem_univ, true_and] at h_y
      rw [h_x, h_y]
    simp only [h_σy, sub_self, zero_mul, neg_zero]
  rw [this, Int.add_zero]
  apply Finset.sum_le_sum
  intro u h_u_notin_S
  by_cases h : num_edges G x u = 0
  · -- Case: num_edges G x u = 0
    simp only [h, CharP.cast_eq_zero, mul_zero, neg_zero, Std.le_refl]
  . -- Case: num_edges G x u ≠ 0
    have h : num_edges G x u > 0 := by
      exact Nat.pos_iff_ne_zero.mpr h
    suffices 1 ≤ σ x - σ u by
      rw [neg_mul_eq_neg_mul]
      simp only [neg_sub, Int.natCast_pos, h, le_mul_iff_one_le_left, this]
    suffices 0 < σ x - σ u by
      exact Int.le_of_sub_one_lt this
    dsimp only [S] at h_u_notin_S; simp only [Finset.mem_filter, mem_univ, true_and] at h_u_notin_S
    rw [h_x]
    specialize w_argmax u (by simp only [mem_univ])
    linarith [lt_of_le_of_ne w_argmax h_u_notin_S]
private lemma q_reducer_of_add_princ_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) (σ : firing_script G) :
  q_reduced G q (D + prin G σ) → q_effective q D → q_reducer G q σ := by
  intro h_q_reduced h_q_effective v
  have h_eff := h_q_reduced.1
  rcases (maxset_of_script G (-σ)) with ⟨S, ⟨w, h_w⟩, h_S⟩
  have q_S : q ∈ S := by
    contrapose! h_q_effective with q_nin_S
    rcases h_q_reduced.exists_lt_outdeg q_nin_S ⟨w, h_w⟩ with
      ⟨v, v_in_S, h_debt⟩
    have dv_neg := lt_of_lt_of_le h_debt (h_S v v_in_S).2
    simp only [Pi.add_apply, map_neg, Pi.neg_apply, neg_neg, add_lt_iff_neg_right] at dv_neg
    unfold q_effective; push Not; use v
    suffices v ≠ q by simp only [ne_eq, this, not_false_eq_true, dv_neg, and_self]
    contrapose! q_nin_S
    rw [← q_nin_S]; exact v_in_S
  have ineq : (-σ) v ≤ (-σ) q := ((h_S q q_S).1 v).1
  repeat rw [Pi.neg_apply] at ineq
  linarith
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution (G : CFGraph) (q : G.V) (D₁ D₂ : CFDiv G) :
  q_reduced G q D₁ ∧ q_reduced G q D₂ ∧ linear_equiv G D₁ D₂ → D₁ = D₂ := by
  intro ⟨h_qred_1,h_qred_2,h_lequiv⟩
  unfold linear_equiv at h_lequiv
  simp only [principal_iff_eq_prin] at h_lequiv
  rcases h_lequiv with ⟨σ, h_D2_eq⟩
  have h_reducer_1 : q_reducer G q σ := by
    apply q_reducer_of_add_princ_reduced G q D₁ σ
    rw [← h_D2_eq]
    simp only [add_sub_cancel]
    exact h_qred_2
    exact h_qred_1.left
  have h_reducer_2 : q_reducer G q (-σ) := by
    apply q_reducer_of_add_princ_reduced G q D₂ (-σ)
    rw [(prin G).map_neg, ← sub_eq_add_neg]
    simp only [← h_D2_eq, sub_sub_cancel]
    exact h_qred_1
    exact h_qred_2.left
  have h_zero : prin G σ = 0 :=
    prin_eq_zero_of_two_sided_reducer G q σ h_reducer_1 h_reducer_2
  rw [h_zero] at h_D2_eq
  apply sub_eq_zero.mp at h_D2_eq
  rw [h_D2_eq]
