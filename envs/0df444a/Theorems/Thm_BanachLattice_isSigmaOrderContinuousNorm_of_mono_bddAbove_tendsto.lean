-- Prove2me | Theorems.Thm_BanachLattice_isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
-- name    : BanachLattice.isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:52.735856+00:00
-- url     : https://prove2.me/theorems/eb9be1dc-db3e-41bb-8bb6-6fe9404dc719
-- title:
--   Banach Lattice: is Sigma Order Continuous Norm of mono bdd Above tendsto
-- statement:
--   A Banach lattice in which every increasing order-bounded sequence
--   converges in norm has a σ-order continuous norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Nakano.lean#L70-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Nakano.lean#L70-L102

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
set_option autoImplicit true
@[expose] public section
public section
open BanachLattice
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable [BanachLattice X]

theorem BanachLattice.isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
    (h : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x)) :
    IsSigmaOrderContinuousNorm X := by sorry
