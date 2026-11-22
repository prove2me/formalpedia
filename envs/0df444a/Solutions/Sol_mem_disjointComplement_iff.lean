-- Prove2me | solution 1 for mem_disjointComplement_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:31:04.203933+00:00
-- url     : https://prove2.me/submissions/c0411b41-3353-4270-a38f-f0b21f34ece8

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
theorem _root_.solution {A : Set X} {x : X} :
    x ∈ Aᵈ ↔ ∀ a ∈ A, IsVLDisjoint x a := Iff.rfl
