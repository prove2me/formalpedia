-- Prove2me | Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
-- name    : ClosedOrderIdeal.sup_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:19.725918+00:00
-- url     : https://prove2.me/theorems/03a1a545-d126-41e2-9deb-564fb88ce118
-- title:
--   Closed Order Ideal: sup to Submodule
-- statement:
--   The underlying submodule of a binary join is the sum of the underlying
--   submodules.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L1120-L1121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L1120-L1121

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

theorem ClosedOrderIdeal.sup_toSubmodule (J₁ J₂ : ClosedOrderIdeal X) :
    (J₁ ⊔ J₂).toSubmodule = J₁.toSubmodule + J₂.toSubmodule := by sorry

attribute [defeq] ClosedOrderIdeal.sup_toSubmodule
