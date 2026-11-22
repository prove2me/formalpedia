-- Prove2me | solution 1 for isVLDisjoint_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:38.568262+00:00
-- url     : https://prove2.me/submissions/b4e60fcf-13eb-4932-9c3a-1c6e24b19c1e

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_comm
public import Theorems.Thm_isVLDisjoint_zero_left

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution (x : X) : IsVLDisjoint x 0 :=
  isVLDisjoint_comm.mpr (isVLDisjoint_zero_left x)
