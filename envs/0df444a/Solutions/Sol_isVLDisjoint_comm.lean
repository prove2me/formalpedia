-- Prove2me | solution 1 for isVLDisjoint_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:27.167704+00:00
-- url     : https://prove2.me/submissions/255dbacd-b9f7-460f-9405-8c2a98f2c43e

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
omit [IsOrderedAddMonoid X]
theorem _root_.solution {x y : X} :
    IsVLDisjoint x y ↔ IsVLDisjoint y x := by
  unfold IsVLDisjoint; rw [inf_comm]
