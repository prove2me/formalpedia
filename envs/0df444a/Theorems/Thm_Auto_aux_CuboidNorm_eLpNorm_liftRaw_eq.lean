-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftRaw_eq
-- name    : Auto.aux_CuboidNorm.eLpNorm_liftRaw_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:13.350812+00:00
-- url     : https://prove2.me/theorems/468a94c7-9726-43cf-9063-594c7bd0a0a6
-- title:
--   aux Cuboid Norm: e Lp Norm lift Raw eq
-- statement:
--   The aux Cuboid Norm construction uses the e Lp Norm lift Raw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1636-L1646
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1636-L1646

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

theorem Auto.aux_CuboidNorm.eLpNorm_liftRaw_eq {n : ℕ} (F : RVector n → ℝ)
    (p : ℝ≥0∞) (hF : Measurable F) :
    eLpNorm (aux_liftRaw F) p volume = eLpNorm F p volume := by sorry
