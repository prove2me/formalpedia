-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_memLp_liftedCuboidEmbed
-- name    : Auto.aux_CuboidNorm.memLp_liftedCuboidEmbed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:41:27.340146+00:00
-- url     : https://prove2.me/theorems/6aeefb83-d54d-47e9-9ece-8b3784da58cb
-- title:
--   aux Cuboid Norm: mem Lp lifted Cuboid Embed
-- statement:
--   The aux Cuboid Norm construction uses the mem Lp lifted Cuboid Embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1702-L1712
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1702-L1712

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.memLp_liftedCuboidEmbed {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    MemLp (aux_liftRaw (aux_cuboidEmbed ε δ i a)) p volume := by sorry
