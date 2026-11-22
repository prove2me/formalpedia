-- Prove2me | Theorems.Thm_BanachLattice_disjoint_bddAbove_tendsto_zero
-- name    : BanachLattice.disjoint_bddAbove_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:50.492168+00:00
-- url     : https://prove2.me/theorems/7443c316-19c8-40a4-a549-54738498184d
-- title:
--   Banach Lattice: disjoint bdd Above tendsto zero
-- statement:
--   In an order continuous Banach lattice, every order-bounded pairwise
--   disjoint sequence converges to zero in norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L721-L786
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L721-L786

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

theorem BanachLattice.disjoint_bddAbove_tendsto_zero [IsOrderContinuousNorm X]
    {u : ℕ → X} (hd : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hbd : BddAbove (Set.range fun n => |u n|)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by sorry
