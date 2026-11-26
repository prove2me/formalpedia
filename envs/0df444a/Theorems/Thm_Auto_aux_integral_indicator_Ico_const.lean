-- Prove2me | Theorems.Thm_Auto_aux_integral_indicator_Ico_const
-- name    : Auto.aux_integral_indicator_Ico_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:05.696079+00:00
-- url     : https://prove2.me/theorems/4ed61e14-4edf-53f2-9030-f46fa82d856a
-- title:
--   Auto: aux integral indicator Ico const
-- statement:
--   Integral of a constant on a half-open real interval.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L851-L855
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L851-L855

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

theorem Auto.aux_integral_indicator_Ico_const {a b c : ℝ} (hab : a ≤ b) :
    ∫ s : ℝ, (Ico a b).indicator (fun _ ↦ c) s = (b - a) * c := by sorry
