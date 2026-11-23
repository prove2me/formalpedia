-- Prove2me | solution 1 for q_effective_to_q_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:47.686651+00:00
-- url     : https://prove2.me/submissions/b5cff94b-28a4-4b15-961c-523a05e5c5ad

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_num_edges_symmetric
public import Theorems.Thm_set_firing_eq_add_prin_indicator_script
public import Theorems.Thm_principal_iff_eq_prin
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_linear_equiv_preserves_deg
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_q_effective_set_firing_of_legal_set
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
private lemma q_reduced_of_no_active (G :CFGraph) {q : G.V} {D : CFDiv G} (h_eff : q_effective q D) (h_no_active : ∀ v : G.V, ¬ active G q D v) :
  q_reduced G q D := by
  contrapose! h_no_active with h_not_q_reduced
  dsimp only [q_reduced, ne_eq] at h_not_q_reduced
  push Not at h_not_q_reduced
  rcases h_not_q_reduced h_eff with ⟨S, q_nin_S, h_S_nonempty, h_outdeg⟩
  -- Construct a firing script that fires all vertices in S
  let σ := indicator_script G S
  have h_reducer : q_reducer G q σ := by
    intro v
    dsimp only [σ, indicator_script]
    simp only [q_nin_S, ↓reduceIte]
    by_cases h : v ∈ S
    simp only [h, ↓reduceIte, zero_le_one]; simp only [h, ↓reduceIte, Std.le_refl]
  use Classical.choose h_S_nonempty
  let h := Classical.choose_spec h_S_nonempty
  dsimp only [active]
  use σ
  refine ⟨h_reducer, ?_, ?_⟩
  · rw [show σ = indicator_script G S from rfl,
      ← set_firing_eq_add_prin_indicator_script]
    exact q_effective_set_firing_of_legal_set G h_eff h_outdeg
  · simp only [σ, indicator_script, q_nin_S, ↓reduceIte, h, zero_lt_one]
private lemma reduction_excess_nonneg (G : CFGraph) {q : G.V} {D : CFDiv G} (h_eff : q_effective q D) :
  0 ≤ reduction_excess G q D := by
  dsimp only [reduction_excess]
  apply Finset.sum_nonneg
  intro v _
  by_cases h_active : active G q D v
  · -- Case: v is active
    simp only [h_active, ↓reduceIte]
    apply h_eff
    intro h_contra
    rw [h_contra] at h_active
    dsimp only [active] at h_active
    rcases h_active with ⟨σ, h_reducer, h_eff', h_ineq⟩
    simp only [lt_self_iff_false] at h_ineq
  · -- Case: v is not active
    simp only [h_active, ↓reduceIte, Std.le_refl]
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) {q : G.V} {D : CFDiv G} (h_eff : q_effective q D) :
  ∃ E : CFDiv G, q_reduced G q E ∧ linear_equiv G D E := by
  -- Use induction on reduction_excess
  classical -- In order to filter using the undecidable "active"
  let S := Finset.univ.filter (λ v : G.V => active G q D v)
  have q_nin_S : q ∉ S := by
    intro h_contra
    dsimp only [S] at h_contra
    simp only [Finset.mem_filter, mem_univ, true_and] at h_contra
    dsimp only [active] at h_contra
    rcases h_contra with ⟨σ, h_reducer, h_ineq⟩
    simp only [lt_self_iff_false, and_false] at h_ineq
  by_cases h_S_empty : S = ∅
  · -- Case: No active vertices, so D is already q-reduced
    use D
    constructor
    · -- q-reducedness
      apply q_reduced_of_no_active G h_eff
      intro v h_contra
      have : v ∈ S := by
        dsimp only [S]
        simp only [Finset.mem_filter, mem_univ, h_contra, and_self]
      rw [h_S_empty] at this
      -- "this" is not v ∈ ∅, a contradiction
      simp only [notMem_empty] at this
    . -- Linear equivalence
      exact linear_equiv.refl G D
  · -- Case: There are active vertices. Choose one on the boundary.
    have : ∃ v : G.V, active G q D v := by
      contrapose! h_S_empty with h_no_active
      dsimp only [S]
      simp only [h_no_active, Finset.filter_false]
    rcases this with ⟨v_active, h_v_active⟩
    have : ∃ (v q : G.V), v ∈ S ∧ q ∉ S := by
      use v_active, q
      simp only [q_nin_S, not_false_eq_true, and_true]
      simp only [Finset.mem_filter, mem_univ, true_and, S]
      exact h_v_active
    have := h_conn S this
    rcases this with ⟨v, v_in_S, w, w_nin_S, h_edge⟩
    -- Fire involving v to get a new divisor D'
    simp only [Finset.mem_filter, mem_univ, true_and, S] at v_in_S
    dsimp only [active] at v_in_S
    rcases v_in_S with ⟨σ, h_reducer, h_eff_S, h_ineq⟩
    let D' := D + prin G (σ)
    have D_equiv_D' : linear_equiv G D D' := by
      unfold linear_equiv
      have : D' - D = prin G σ := by
        simp only [add_sub_cancel_left, D']
      rw [this]
      apply (principal_iff_eq_prin G (prin G σ)).mpr ⟨σ,rfl⟩

    -- Facts about D', needed for induction
    have h_eff' : q_effective q D' := by
      intro x x_ne_q
      dsimp only [Pi.add_apply, D']
      exact h_eff_S x x_ne_q

    have h_active_shrinks (x : G.V): active G q D' x → active G q D x := by
      intro h_active_D'
      dsimp only [active]
      rcases h_active_D' with ⟨σ', h_reducer', h_eff'', h_ineq'⟩
      use σ + σ'
      constructor
      · -- Show q_reducer
        intro y
        repeat rw [Pi.add_apply]
        apply add_le_add (h_reducer y) (h_reducer' y)
      constructor
      · -- Show q_effective
        intro z z_ne_q
        dsimp only [D'] at h_eff''
        specialize h_eff'' z z_ne_q
        rw [(prin G).map_add, ← add_assoc]
        exact h_eff''
      · -- Show chips are fired from x
        repeat rw [Pi.add_apply]
        apply add_lt_add_of_le_of_lt
        exact h_reducer x
        exact h_ineq'

    have chips_to_inactive_per_edge (u x : G.V) : ¬ active G q D x → (σ u - σ x) * ↑(num_edges G x u) ≥ 0 := by
      intro h_inactive_D
      simp only [ge_iff_le]
      apply mul_nonneg
      · -- Show σ u - σ x ≥ 0
        have : σ x ≤ σ q := by
          dsimp only [active] at h_inactive_D
          push Not at h_inactive_D
          specialize h_inactive_D σ
          exact h_inactive_D h_reducer h_eff'
        have : σ u ≥ σ q := by
          specialize h_reducer u
          linarith
        linarith
      · -- Show num_edges G x u ≥ 0
        simp only [Nat.cast_nonneg]

    have chips_to_inactive (x : G.V) : ¬ active G q D x → D x ≤ D' x := by
      -- Goal: 0 ≤ ∑ (σ u - σ x) * num_edges G x u
      intro h_inactive_D
      simp only [Pi.add_apply, prin_apply, D']
      simp only [le_add_iff_nonneg_right]
      apply Finset.sum_nonneg
      intro u _
      exact chips_to_inactive_per_edge u x h_inactive_D

    have h_smaller : reduction_excess G q D' < reduction_excess G q D := by
      dsimp only [reduction_excess]
      repeat rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      -- First, pass to a sum over non-active vertices
      have h (D : CFDiv G) : ∑ x ∈ Finset.filter (active G q D) univ, D x = deg D - ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x := by
        dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => active G q D v)]
        simp only [add_sub_cancel_right]
      rw [h D', h D]
      have : deg D = deg D' :=
        linear_equiv_preserves_deg G D D' D_equiv_D'
      rw [← this]
      simp only [sub_lt_sub_iff_left, gt_iff_lt]
      -- Write as a sum over all vertices in order to compare terms
      have h (D : CFDiv G) : ∑ x ∈ Finset.filter (fun v => ¬ active G q D v) univ, D x = ∑ x : G.V, if ¬ active G q D x then D x else 0 := by
        rw [Finset.sum_filter]
      rw [h D', h D]
      -- Now compare term-by-term
      apply Finset.sum_lt_sum
      -- Show each term is ≤ the corresponding term
      intro x _
      by_cases h_active_D' : active G q D' x
      · -- Case: x is active in D'. Then already active in D.
        have h_active_D := h_active_shrinks x h_active_D'
        simp only [h_active_D, not_true_eq_false, ↓reduceIte, h_active_D', Std.le_refl]
      · -- Case: x is not active in D'.
        simp only [ite_not, h_active_D', not_false_eq_true, ↓reduceIte]
        by_cases h_active_D : active G q D x
        · -- Subcase: x is active in D
          simp only [h_active_D, ↓reduceIte]
          -- Show 0 ≤ D' x
          apply h_eff' x
          intro h_contra
          rw [h_contra] at h_active_D
          dsimp only [S] at q_nin_S
          simp only [Finset.mem_filter, mem_univ, true_and] at q_nin_S
          contradiction
        · -- Subcase: x is not active in D either
          simp only [h_active_D, ↓reduceIte]
          -- Show D x ≤ D' x
          exact chips_to_inactive x h_active_D
      -- Now, show that strict inequality holds for at least one term
      use w
      have h_inactive_D : ¬ active G q D w := by
        dsimp only [S] at w_nin_S
        simp only [Finset.mem_filter, mem_univ, true_and] at w_nin_S
        exact w_nin_S
      have h_active_D' : ¬ active G q D' w := by
        contrapose! h_inactive_D with h_active_D'
        exact (h_active_shrinks w) h_active_D'
      simp only [mem_univ, h_inactive_D, not_false_eq_true, ↓reduceIte, h_active_D', true_and,
          gt_iff_lt]
      -- Show D w < D' w
      simp only [Pi.add_apply, prin_apply, D']
      simp only [lt_add_iff_pos_right]
      -- Goal: 0 < ∑ (σ u - σ w) * num_edges
      apply Finset.sum_pos'
      -- Show each term is nonnegative
      intro u _
      exact chips_to_inactive_per_edge u w h_inactive_D
      -- Show at least one term is positive
      use v
      simp only [mem_univ, true_and]
      -- Goal: (σ v - σ w) * num_edges G w v > 0
      apply Int.mul_pos
      · -- Show σ v - σ w > 0
        have : σ w ≤ σ q := by
          dsimp only [active] at h_inactive_D
          push Not at h_inactive_D
          specialize h_inactive_D σ
          exact h_inactive_D h_reducer h_eff'
        linarith [this, h_ineq]
      . -- Show num_edges G w v > 0
        rw [← num_edges_symmetric G v w]
        simp only [Int.natCast_pos, h_edge]
    have ih := solution h_conn h_eff'
    rcases ih with ⟨E, h_q_reduced, h_lequiv⟩
    use E
    constructor
    · -- q-reducedness
      exact h_q_reduced
    · -- Linear equivalence
      exact D_equiv_D'.trans h_lequiv
termination_by (reduction_excess G q D).toNat
decreasing_by
  -- Some effort needed to deal with ℤ versus ℕ
  rw [Int.toNat_lt]
  simp only [Int.ofNat_toNat, lt_sup_iff]
  dsimp only [D'] at h_smaller
  left
  exact h_smaller
  exact reduction_excess_nonneg G h_eff'
