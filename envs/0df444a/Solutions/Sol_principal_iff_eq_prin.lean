-- Prove2me | solution 1 for principal_iff_eq_prin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:42:47.326114+00:00
-- url     : https://prove2.me/submissions/fb4aaaed-c170-45e9-91ff-530bcde4f012

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_num_edges_symmetric
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
private lemma mem_principal_divisors_firing_vector (G : CFGraph) (v : G.V) :
  firing_vector G v ∈ principal_divisors G := AddSubgroup.subset_closure (Set.mem_range_self v)
open Matrix
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
theorem _root_.solution (G : CFGraph) (D : CFDiv G) :
  D ∈ principal_divisors G ↔ ∃ σ : firing_script G, D = prin G σ := by
  unfold principal_divisors
  constructor
  · -- Forward direction
    intro h_inp
    -- Use the defining property of a subgroup closure
    refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_inp
    . -- Case 1: h_inp is a firing vector
      intro x h_firing
      rcases h_firing with ⟨v, rfl⟩
      let σ : firing_script G := λ u => if u = v then 1 else 0
      use σ
      unfold firing_vector prin
      funext w
      dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, σ]
      by_cases h_eq : w = v
      . -- Case w = v
        simp only [h_eq, ↓reduceIte]
        unfold vertex_degree
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro u _
        by_cases h_eq2 : u = v <;> simp only [h_eq2, num_edges_self_zero, CharP.cast_eq_zero,
            neg_zero, ↓reduceIte, sub_self, mul_zero, zero_sub, Int.reduceNeg, neg_mul, one_mul]
      . -- Case w ≠ v
        simp only [h_eq, ↓reduceIte, num_edges_symmetric G v w, sub_zero, ite_mul, one_mul,
            zero_mul, sum_ite_eq', mem_univ]
    . -- Case 2: h_inp is zero divisor
      use 0
      simp only [_root_.map_zero]
    . -- Case 3: h_inp is a sum of two principal divisors
      intros x y _ _ h_x_prin h_y_prin
      rcases h_x_prin with ⟨σ₁, h_x_eq⟩
      rcases h_y_prin with ⟨σ₂, h_y_eq⟩
      rw [h_x_eq, h_y_eq]
      use σ₁ + σ₂
      simp only [_root_.map_add]
    . -- Case 4: h_inp is negation of a principal divisor
      intro x _ h_x_prin
      rcases h_x_prin with ⟨σ, h_x_eq⟩
      use -σ
      rw [h_x_eq]
      simp only [map_neg]
  . -- Backward direction
    intro h_prin
    rcases h_prin with ⟨σ, h_eq⟩
    unfold prin at h_eq
    let D₁ := ∑ u : G.V, (σ u) • (firing_vector G u)
    have D1_principal :D₁ ∈ principal_divisors G := by
      apply AddSubgroup.sum_mem _ _
      intro u _
      apply AddSubgroup.zsmul_mem _ _
      exact mem_principal_divisors_firing_vector G u
    have D_eq : D₁ = D := by
      rw [h_eq]
      funext v
      -- expand the definition of D₁
      dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, D₁]
      unfold firing_vector
      -- Move that v into the sum on the left side
      simp only [Finset.sum_apply]
      simp only [Pi.smul_apply, Int.zsmul_eq_mul, mul_ite, mul_neg]
      have: ∀ (u : G.V), (σ u - σ v) * ↑(num_edges G v u) = σ u * ↑(num_edges G v u) - σ v * ↑(num_edges G v u) := by intro u; ring
      simp only [this]

      have h (x : G.V) : (if v = x then -(σ x * vertex_degree G x) else σ x * ↑(num_edges G x v) ) = σ x * (↑(num_edges G x v) ) - σ x * ( (if v = x then vertex_degree G x else 0))  := by
        by_cases h : v = x <;> simp only [h, ↓reduceIte, mul_zero, sub_zero, num_edges_self_zero,
            CharP.cast_eq_zero, zero_sub]

      simp only [h]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      suffices ∑ x : G.V, σ x * (if v = x then vertex_degree G x else 0) = ∑ x : G.V, (σ v * ↑(num_edges G v x)) by
        rw [this]
        simp only [num_edges_symmetric]

      dsimp only [vertex_degree]
      rw [← Finset.mul_sum]
      simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
    rw [← D_eq]
    exact D1_principal
