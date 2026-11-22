-- Prove2me | Theorems.Thm_BanachLattice_isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice
-- name    : BanachLattice.isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:53.549086+00:00
-- url     : https://prove2.me/theorems/e4ae3366-81fb-4388-85af-0b1ee2b642d4
-- title:
--   Banach Lattice: is Order Continuous Norm of is Sigma Conditionally Complete Lattice
-- statement:
--   A Banach lattice that is σ-conditionally complete and has σ-order
--   continuous norm has an order continuous norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Nakano.lean#L138-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Nakano.lean#L138-L222

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
set_option autoImplicit true
@[expose] public section
public section
open BanachLattice
variable {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X] [IsSigmaOrderContinuousNorm X]

theorem BanachLattice.isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice :
    IsOrderContinuousNorm X := by sorry
