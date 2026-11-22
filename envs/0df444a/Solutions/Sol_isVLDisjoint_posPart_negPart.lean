-- Prove2me | solution 1 for isVLDisjoint_posPart_negPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:29.002527+00:00
-- url     : https://prove2.me/submissions/01272c8f-7787-408c-a131-444e43abd897

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_of_inf_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution (x : X) : IsVLDisjoint x⁺ x⁻ :=
  isVLDisjoint_of_inf_eq_zero (posPart_inf_negPart_eq_zero x)
