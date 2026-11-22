-- Prove2me | Theorems.Thm_Band_abs_mem
-- name    : Band.abs_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:29:44.247685+00:00
-- url     : https://prove2.me/theorems/6661da93-25ac-4929-a45b-074cdbb3bd27
-- title:
--   Band: abs mem
-- statement:
--   A band is closed under absolute value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L80-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L80-L81

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Theorems.Thm_VectorSublattice_abs_mem

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open Band
variable (B : Band X)

theorem Band.abs_mem {x : X} (hx : x ∈ B) : |x| ∈ B := by sorry
