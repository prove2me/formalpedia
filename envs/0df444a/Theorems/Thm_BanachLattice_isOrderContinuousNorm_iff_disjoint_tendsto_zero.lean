-- Prove2me | Theorems.Thm_BanachLattice_isOrderContinuousNorm_iff_disjoint_tendsto_zero
-- name    : BanachLattice.isOrderContinuousNorm_iff_disjoint_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:31.902382+00:00
-- url     : https://prove2.me/theorems/18994861-5885-4c89-91d4-e1325c59616a
-- title:
--   Banach Lattice: is Order Continuous Norm iff disjoint tendsto zero
-- statement:
--   **Meyer-Nieberg theorem**: a Banach lattice has an order continuous norm
--   iff every order-bounded pairwise disjoint sequence converges to zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L837-L844
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L837-L844

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

theorem BanachLattice.isOrderContinuousNorm_iff_disjoint_tendsto_zero :
    IsOrderContinuousNorm X ↔
      (∀ {u : ℕ → X},
        Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
        BddAbove (Set.range fun n => |u n|) →
        Filter.Tendsto u Filter.atTop (nhds 0)) := by sorry
