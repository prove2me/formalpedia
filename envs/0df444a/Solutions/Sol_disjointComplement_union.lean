-- Prove2me | solution 1 for disjointComplement_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:30:49.611346+00:00
-- url     : https://prove2.me/submissions/b524569b-546c-4067-9b63-19c72a6931af

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
theorem _root_.solution (A B : Set X) :
    (A ∪ B)ᵈ = Aᵈ ∩ Bᵈ := by
  ext x
  refine ⟨fun hx => ⟨fun a ha => hx a (Or.inl ha), fun b hb => hx b (Or.inr hb)⟩,
    fun ⟨hA, hB⟩ _ hy => ?_⟩
  rcases hy with hy | hy
  · exact hA _ hy
  · exact hB _ hy
