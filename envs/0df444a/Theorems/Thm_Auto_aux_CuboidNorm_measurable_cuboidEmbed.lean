-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_measurable_cuboidEmbed
-- name    : Auto.aux_CuboidNorm.measurable_cuboidEmbed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:26.776806+00:00
-- url     : https://prove2.me/theorems/902c0403-a2eb-4aee-abb3-55e0bbdeb65a
-- title:
--   aux Cuboid Norm: measurable cuboid Embed
-- statement:
--   The aux Cuboid Norm construction uses the measurable cuboid Embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1600-L1612
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1600-L1612

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

theorem Auto.aux_CuboidNorm.measurable_cuboidEmbed {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) :
    Measurable (aux_cuboidEmbed ε δ i a) := by sorry
