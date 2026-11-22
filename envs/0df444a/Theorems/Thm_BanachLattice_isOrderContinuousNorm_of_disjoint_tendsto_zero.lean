-- Prove2me | Theorems.Thm_BanachLattice_isOrderContinuousNorm_of_disjoint_tendsto_zero
-- name    : BanachLattice.isOrderContinuousNorm_of_disjoint_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:21.503801+00:00
-- url     : https://prove2.me/theorems/6e9e915e-8740-4d80-b467-b7b9dd7e0cd4
-- title:
--   Banach Lattice: is Order Continuous Norm of disjoint tendsto zero
-- statement:
--   A Banach lattice whose order-bounded pairwise disjoint sequences all
--   converge to zero in norm has an order continuous norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L790-L833
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L790-L833

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open BanachLattice
variable [BanachLattice X]

theorem BanachLattice.isOrderContinuousNorm_of_disjoint_tendsto_zero
    (h : ∀ {u : ℕ → X},
      Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
      BddAbove (Set.range fun n => |u n|) →
      Filter.Tendsto u Filter.atTop (nhds 0)) :
    IsOrderContinuousNorm X := by sorry
