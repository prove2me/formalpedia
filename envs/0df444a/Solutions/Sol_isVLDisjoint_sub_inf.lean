-- Prove2me | solution 1 for isVLDisjoint_sub_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:31.216341+00:00
-- url     : https://prove2.me/submissions/3006824e-3a48-47b5-9a3c-d9846ec86dbe

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_posPart_negPart
public import Theorems.Thm_sub_inf_eq_posPart


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution (x y : X) :
    IsVLDisjoint (x - x ⊓ y) (y - x ⊓ y) := by
  have h1 : x - x ⊓ y = (x - y)⁺ := sub_inf_eq_posPart x y
  have h2 : y - x ⊓ y = (x - y)⁻ := by
    rw [inf_comm, sub_inf_eq_posPart, negPart_def, neg_sub, posPart_def]
  rw [h1, h2]
  exact isVLDisjoint_posPart_negPart (x - y)
