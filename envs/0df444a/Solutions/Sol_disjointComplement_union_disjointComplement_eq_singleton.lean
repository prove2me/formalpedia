-- Prove2me | solution 1 for disjointComplement_union_disjointComplement_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:31:57.193816+00:00
-- url     : https://prove2.me/submissions/fc74b600-d87e-47f7-af6f-a2614932c044

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
public import Theorems.Thm_disjointComplement_inter_eq_zero
public import Theorems.Thm_isVLDisjoint_zero_left


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [VectorLattice X]
theorem _root_.solution (A : Set X) :
    (A ∪ Aᵈ)ᵈ = ({0} : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxA : x ∈ Aᵈ := fun a ha => hx a (Or.inl ha)
    have hxAd : x ∈ Aᵈᵈ := fun a ha => hx a (Or.inr ha)
    exact disjointComplement_inter_eq_zero Aᵈ ⟨hxA, hxAd⟩
  · rintro x rfl a _
    exact isVLDisjoint_zero_left a
