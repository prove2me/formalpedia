-- Prove2me | solution 1 for divisor_reverse_orientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:32.780797+00:00
-- url     : https://prove2.me/submissions/b8c6c3f4-58bb-4903-9db2-4778db9e9cf9

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma flow_reverse {G : CFGraph} (O : CFOrientation G) (v w : G.V) :
  flow (O.reverse G) v w = flow O w v :=
  count_map_swap O.directed_edges v w
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} (O : CFOrientation G)  : ordiv G O + ordiv G (O.reverse) = canonical_divisor G := by
  let O' := O.reverse
  funext v
  rw [Pi.add_apply]
  dsimp only [ordiv, canonical_divisor]
  suffices indeg G O v + indeg G O' v = vertex_degree G v by
    dsimp only [vertex_degree] at this ⊢
    rw [← this]
    ring
  rw [indeg_eq_sum_flow, indeg_eq_sum_flow, Nat.cast_sum, Nat.cast_sum]
  dsimp only [vertex_degree]
  rw [← sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [← opp_flow O v w]
  rw [Nat.cast_add, add_comm]
  simp only [add_left_inj, Nat.cast_inj]
  -- Goal is now: flow O' w v = flow O v w
  rw [flow_reverse O w v]
