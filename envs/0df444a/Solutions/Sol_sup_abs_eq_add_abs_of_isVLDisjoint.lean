-- Prove2me | solution 1 for sup_abs_eq_add_abs_of_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:43.256479+00:00
-- url     : https://prove2.me/submissions/b1a96655-f116-4c11-9da9-528f4f7f144c

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
    (h : IsVLDisjoint x y) : |x| ⊔ |y| = |x| + |y| := by
  have := inf_add_sup |x| |y|
  rw [show |x| ⊓ |y| = 0 from h, zero_add] at this
  exact this
