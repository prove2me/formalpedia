-- Prove2me | Theorems.Thm_ClosedOrderIdeal_mem_sInf
-- name    : ClosedOrderIdeal.mem_sInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:09.038505+00:00
-- url     : https://prove2.me/theorems/361906ea-80ba-483c-a6b6-25733735a5d3
-- title:
--   Closed Order Ideal: mem s Inf
-- statement:
--   Membership in an arbitrary intersection of closed order ideals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L1106-L1111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L1106-L1111

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

theorem ClosedOrderIdeal.mem_sInf {S : Set (ClosedOrderIdeal X)} {x : X} :
    x ∈ (InfSet.sInf S : ClosedOrderIdeal X) ↔ ∀ J ∈ S, x ∈ J := by sorry
