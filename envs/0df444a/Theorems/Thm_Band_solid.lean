-- Prove2me | Theorems.Thm_Band_solid
-- name    : Band.solid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:29:43.371653+00:00
-- url     : https://prove2.me/theorems/ff2b05cf-b3e0-4012-a968-ebbd7a862c7c
-- title:
--   Band: solid
-- statement:
--   A band is solid.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L75-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L75-L77

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

theorem Band.solid {x y : X} (hx : x ∈ B) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    y ∈ B := by sorry
