-- Prove2me | solution 1 for isVLDisjoint_of_inf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:39.653891+00:00
-- url     : https://prove2.me/submissions/3db3a943-a302-488e-955f-d0570b4f7cba

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {x y : X}
    (h : x ⊓ y = 0) : IsVLDisjoint x y := by
  have hx : 0 ≤ x := h ▸ inf_le_left
  have hy : 0 ≤ y := h ▸ inf_le_right
  unfold IsVLDisjoint; rwa [abs_of_nonneg hx, abs_of_nonneg hy]
