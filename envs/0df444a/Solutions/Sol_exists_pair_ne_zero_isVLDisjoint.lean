-- Prove2me | solution 1 for exists_pair_ne_zero_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:38.27739+00:00
-- url     : https://prove2.me/submissions/f697f254-e14c-470b-b2ed-628dfd79755a

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_posPart_negPart
public import Theorems.Thm_exists_not_nonneg_not_nonpos_of_one_lt_rank


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
theorem _root_.solution [IsVLArchimedean X]
    (h : 1 < Module.rank ℝ X) :
    ∃ u v : X, u ≠ 0 ∧ v ≠ 0 ∧ IsVLDisjoint u v := by
  obtain ⟨x, hxp, hxn⟩ := exists_not_nonneg_not_nonpos_of_one_lt_rank h
  refine ⟨x⁺, x⁻, ?_, ?_, isVLDisjoint_posPart_negPart x⟩
  · exact fun h => hxn (posPart_eq_zero.mp h)
  · exact fun h => hxp (negPart_eq_zero.mp h)
