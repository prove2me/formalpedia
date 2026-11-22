-- Prove2me | solution 1 for subset_disjointComplement_disjointComplement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:30:46.300244+00:00
-- url     : https://prove2.me/submissions/bc6f6c9a-41f2-4303-87f1-86a72ba9ee28

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
public import Theorems.Thm_isVLDisjoint_comm


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [IsOrderedAddMonoid X] [VectorLattice X]
theorem _root_.solution (A : Set X) :
    A ⊆ Aᵈᵈ := fun a ha _ hy => isVLDisjoint_comm.mp (hy a ha)
