-- Prove2me | solution 1 for isVLDisjoint_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:38.381118+00:00
-- url     : https://prove2.me/submissions/01f28d30-2c21-42c6-becb-be873a8faadc

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution (x : X) : IsVLDisjoint 0 x := by
  unfold IsVLDisjoint; simp [abs_zero]
