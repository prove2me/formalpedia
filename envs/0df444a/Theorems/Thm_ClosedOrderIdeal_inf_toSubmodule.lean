-- Prove2me | Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
-- name    : ClosedOrderIdeal.inf_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:17.401602+00:00
-- url     : https://prove2.me/theorems/72ea681a-94cc-4390-993c-9c7b173ca1bd
-- title:
--   Closed Order Ideal: inf to Submodule
-- statement:
--   The underlying submodule of a binary meet is the intersection of the
--   underlying submodules.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L1115-L1116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L1115-L1116

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open ClosedOrderIdeal
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

theorem ClosedOrderIdeal.inf_toSubmodule (J₁ J₂ : ClosedOrderIdeal X) :
    (J₁ ⊓ J₂).toSubmodule = J₁.toSubmodule ⊓ J₂.toSubmodule := by sorry

attribute [defeq] ClosedOrderIdeal.inf_toSubmodule
