-- Prove2me | solution 1 for zero_divisor_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:51:12.593333+00:00
-- url     : https://prove2.me/submissions/461631e1-1dde-4eab-a0f8-0777d3aa628f

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_winnable_of_effective
public import Theorems.Thm_rank_nonneg_iff_winnable
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma rank_eq_iff (G : CFGraph) (D : CFDiv G) (r : ℤ) :
  rank_eq G D r ↔ rank G D = r := by
  dsimp only [rank_eq]
  have split_eq x: x = r ↔ (x ≥ r ∧ ¬(x ≥ r + 1)) := by
    rw [not_le]
    rw [Int.lt_add_one_iff]
    have helper := @le_antisymm_iff _ _ x r
    rw [helper, and_comm]
  rw [split_eq (rank G D)]
  rw [rank_geq_iff G D r, rank_geq_iff G D (r+1)]
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) : rank G (0:CFDiv G) = 0 := by
  rw [← rank_eq_iff]
  constructor
  have h_eff : effective (0:CFDiv G) := by
    simp only [effective, Pi.zero_apply, ge_iff_le, Std.le_refl, implies_true]
  rw [rank_nonneg_iff_winnable G (0:CFDiv G)]
  exact winnable_of_effective G (0:CFDiv G) h_eff
  have ineq := rank_le_degree G (0:CFDiv G) 1 (by norm_num)
  simp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, sum_const_zero, Int.reduceLE,
      imp_false] at ineq
  exact ineq
