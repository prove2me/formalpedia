-- Prove2me | Theorems.Thm_Band_mem_of_abs_mem
-- name    : Band.mem_of_abs_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:29:47.829637+00:00
-- url     : https://prove2.me/theorems/5f713f06-2fc7-4ef5-b3ad-753353b9c944
-- title:
--   Band: mem of abs mem
-- statement:
--   Membership in a band is equivalent to membership of the absolute value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L84-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L84-L85

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open Band
variable (B : Band X)

theorem Band.mem_of_abs_mem {x : X} (h : |x| ∈ B) : x ∈ B := by sorry
