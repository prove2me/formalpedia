-- Prove2me | solution 1 for winnable_iff_q_reduced_effective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:51:14.401281+00:00
-- url     : https://prove2.me/submissions/7f0b1e59-547a-4f8f-9e75-ed72c0638da7

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
public import Theorems.Thm_unique_q_reduced
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
private lemma reduces_to_q_mono (G : CFGraph) (q : G.V) {D₁ D₂ : CFDiv G} :
  reduces_to G q D₁ D₂ → D₁ q ≤ D₂ q := by
  rintro ⟨σ, h_reducer, h_eq⟩
  have h_prin_q : (prin G σ) q ≥ 0 := by
    rw [prin_apply]
    apply Finset.sum_nonneg
    intro e _
    apply mul_nonneg
    linarith [h_reducer e]
    exact Int.natCast_nonneg _
  rw [h_eq, Pi.add_apply]
  linarith
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
private lemma maximum_of_q_reduced (G : CFGraph) {q : G.V} {D : CFDiv G} : q_reduced G q D → ∀ D' : CFDiv G, linear_equiv G D D' → q_effective q D' → reduces_to G q D' D := by
  intro h_q_reduced D' h_lequiv h_eff
  unfold linear_equiv at h_lequiv
  obtain ⟨σ, hσ⟩ := (principal_iff_eq_prin G (D'-D)).mp h_lequiv
  have D_eq : D = D' + (prin G) (-σ) := by
    rw [map_neg, ←hσ]
    abel
  have hred := q_reducer_of_add_princ_reduced G q D' (-σ) (by rwa [← D_eq]) h_eff
  use (-σ), hred, D_eq
private lemma q_reduced_of_effective_is_effective (G : CFGraph) (q : G.V) (E E' : CFDiv G) :
  effective E → linear_equiv G E E' → q_reduced G q E' → effective E' := by
  intro h_eff h_equiv h_qred
  -- E' is the maximum of its class, so E reduces to E'; chips at q only increase along
  -- the order, and chips away from q are nonnegative since E' is q-effective.
  have h_qeff : q_effective q E := fun v _ => h_eff v
  have h_red : reduces_to G q E E' :=
    maximum_of_q_reduced G h_qred E h_equiv.symm h_qeff
  intro v
  by_cases hvq : v = q
  · rw [hvq]
    linarith [h_eff q, reduces_to_q_mono G q h_red]
  · exact h_qred.1 v hvq
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, linear_equiv G D D' ∧ q_reduced G q D' ∧ effective D' := by
  constructor
  { -- Forward direction
    intro h_win
    rcases h_win with ⟨E, h_eff, h_equiv⟩
    rcases unique_q_reduced h_conn q D with ⟨D', h_D'⟩
    use D'
    constructor
    · exact h_D'.1.1  -- D is linearly equivalent to D'
    constructor
    · exact h_D'.1.2  -- D' is q-reduced
    · -- D' is effective: E ~ D ~ D', and the q-reduced form of an effective divisor
      -- is effective
      exact q_reduced_of_effective_is_effective G q E D' h_eff
        (h_equiv.symm.trans h_D'.1.1) h_D'.1.2
  }
  { -- Reverse direction
    intro h
    rcases h with ⟨D', h_equiv, h_qred, h_eff⟩
    use D'
    exact ⟨h_eff, h_equiv⟩
  }
