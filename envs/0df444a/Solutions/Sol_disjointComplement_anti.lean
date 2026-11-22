-- Prove2me | solution 1 for disjointComplement_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:30:46.952869+00:00
-- url     : https://prove2.me/submissions/76568c59-d50d-4335-be3f-a6339fd0f083

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [IsOrderedAddMonoid X] [VectorLattice X]
theorem _root_.solution {A B : Set X} (h : A ⊆ B) :
    Bᵈ ⊆ Aᵈ := fun _ hx a ha => hx a (h ha)
