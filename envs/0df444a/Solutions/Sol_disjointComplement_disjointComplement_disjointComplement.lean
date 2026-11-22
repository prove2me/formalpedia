-- Prove2me | solution 1 for disjointComplement_disjointComplement_disjointComplement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:31:55.829205+00:00
-- url     : https://prove2.me/submissions/31e60345-6113-4e31-bea1-54338bd85e6a

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
public import Theorems.Thm_disjointComplement_anti
public import Theorems.Thm_subset_disjointComplement_disjointComplement

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [IsOrderedAddMonoid X] [VectorLattice X]
theorem _root_.solution (A : Set X) :
    Aᵈᵈᵈ = Aᵈ :=
  Set.Subset.antisymm
    (disjointComplement_anti (subset_disjointComplement_disjointComplement A))
    (subset_disjointComplement_disjointComplement Aᵈ)
