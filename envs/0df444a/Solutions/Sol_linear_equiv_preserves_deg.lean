-- Prove2me | solution 1 for linear_equiv_preserves_deg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:42:48.819573+00:00
-- url     : https://prove2.me/submissions/73b717d1-d935-4e33-8c88-6a0a087ea5c2

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
attribute [local simp] deg_one_chip
section
@[expose] public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
private lemma deg_firing_vector_eq_zero (G : CFGraph) (v_fire : G.V) :
  deg (firing_vector G v_fire) = 0 := by
  dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, firing_vector]
  rw [Finset.sum_ite]
  have h_filter_eq_single : Finset.filter (fun x => x = v_fire) univ = {v_fire} := by
    ext x; simp only [eq_comm, Finset.mem_filter, mem_univ, true_and, Finset.mem_singleton]
  rw [h_filter_eq_single, Finset.sum_singleton]
  have h_filter_eq_erase : Finset.filter (fun x => ¬x = v_fire) univ = Finset.univ.erase v_fire := by
    ext x
    simp only [Finset.mem_filter, mem_univ, true_and, mem_erase, and_true]
  rw [h_filter_eq_erase]
  simp only [vertex_degree, mem_univ, sum_erase_eq_sub, num_edges_self_zero, CharP.cast_eq_zero,
      sub_zero, neg_add_cancel]
private lemma degree_of_principal_divisor_is_zero (G : CFGraph) (h : CFDiv G) :
  h ∈ principal_divisors G → deg h = 0 := by
  intro h_mem_princ
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ h_mem_princ
  · rintro x ⟨v, rfl⟩
    exact deg_firing_vector_eq_zero G v
  · simp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, sum_const_zero]
  · intro x y _ _ hx hy
    rw [deg.map_add, hx, hy, add_zero]
  · intro x _ hx
    rw [deg.map_neg, hx, neg_zero]
open Matrix
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
theorem _root_.solution (G : CFGraph) (D D' : CFDiv G) (h_equiv : linear_equiv G D D') :
  deg D = deg D' := by
  unfold linear_equiv at h_equiv
  apply degree_of_principal_divisor_is_zero at h_equiv
  rw [map_sub] at h_equiv
  linarith
