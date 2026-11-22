-- Prove2me | Theorems.Thm_Band_inf_mem
-- name    : Band.inf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:29:38.946048+00:00
-- url     : https://prove2.me/theorems/b6ba652b-a3ae-4115-b258-1ddc2f4d6cf3
-- title:
--   Band: inf mem
-- statement:
--   A band is closed under `⊓`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L70-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/Basic.lean#L70-L72

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

theorem Band.inf_mem {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    x ⊓ y ∈ B := by sorry
