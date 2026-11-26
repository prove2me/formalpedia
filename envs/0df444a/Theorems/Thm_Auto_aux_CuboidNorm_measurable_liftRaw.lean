-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_measurable_liftRaw
-- name    : Auto.aux_CuboidNorm.measurable_liftRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:49.520221+00:00
-- url     : https://prove2.me/theorems/654059dd-7260-4923-8d95-4782d73a67d6
-- title:
--   aux Cuboid Norm: measurable lift Raw
-- statement:
--   The aux Cuboid Norm construction uses the measurable lift Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1630-L1634
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1630-L1634

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

theorem Auto.aux_CuboidNorm.measurable_liftRaw {n : ℕ} {F : RVector n → ℝ}
    (hF : Measurable F) :
    Measurable (aux_liftRaw F) := by sorry
