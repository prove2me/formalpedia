-- Prove2me | Theorems.Thm_Band_mem_of_abs_le_abs
-- name    : Band.mem_of_abs_le_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:29:46.507843+00:00
-- url     : https://prove2.me/theorems/6dc8f4c7-4fd7-4667-9f2a-5828ba5ac58c
-- title:
--   Band: mem of abs le abs
-- statement:
--   Solidity in terms of absolute value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L88-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L88-L90

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Theorems.Thm_OrderIdeal_mem_of_abs_le_abs

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open Band
variable (B : Band X)

theorem Band.mem_of_abs_le_abs {x y : X} (hx : x ∈ B) (h : |y| ≤ |x|) :
    y ∈ B := by sorry
