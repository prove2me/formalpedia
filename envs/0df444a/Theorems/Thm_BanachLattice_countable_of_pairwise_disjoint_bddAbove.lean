-- Prove2me | Theorems.Thm_BanachLattice_countable_of_pairwise_disjoint_bddAbove
-- name    : BanachLattice.countable_of_pairwise_disjoint_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:32.551804+00:00
-- url     : https://prove2.me/theorems/2da4e621-f9ad-4f0a-8368-121f9de1a506
-- title:
--   Banach Lattice: countable of pairwise disjoint bdd Above
-- statement:
--   In an order continuous Banach lattice, any order-bounded set of pairwise
--   disjoint non-zero elements is at most countable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L848-L893
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L848-L893

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

theorem BanachLattice.countable_of_pairwise_disjoint_bddAbove [IsOrderContinuousNorm X]
    {S : Set X} (h0 : ∀ x ∈ S, x ≠ 0)
    (hd : S.Pairwise (fun x y => IsVLDisjoint x y))
    (hbd : BddAbove ((fun x => |x|) '' S)) :
    S.Countable := by sorry
