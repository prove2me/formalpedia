-- Prove2me | solution 1 for inf_eq_zero_of_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:39.022802+00:00
-- url     : https://prove2.me/submissions/d9fc4888-4906-4a58-bf39-b1fae80176ff

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : IsVLDisjoint x y) : x ⊓ y = 0 := by
  unfold IsVLDisjoint at h; rwa [abs_of_nonneg hx, abs_of_nonneg hy] at h
