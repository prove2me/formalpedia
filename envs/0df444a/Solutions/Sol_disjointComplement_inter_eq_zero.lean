-- Prove2me | solution 1 for disjointComplement_inter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:30:45.510227+00:00
-- url     : https://prove2.me/submissions/ad23684c-7489-437b-8e55-41277baa3a2b

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
public import Theorems.Thm_abs_eq_zero_iff_zero


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [VectorLattice X]
theorem _root_.solution (A : Set X) :
    A ∩ Aᵈ ⊆ {0} := by
  rintro a ⟨ha, had⟩
  have hd : |a| ⊓ |a| = 0 := had a ha
  rw [inf_idem] at hd
  exact (abs_eq_zero_iff_zero a).mp hd
