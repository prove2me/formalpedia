-- Prove2me | Theorems.Thm_Auto_abs_inv_sin_sub_le
-- name    : Auto.abs_inv_sin_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:57.673257+00:00
-- url     : https://prove2.me/theorems/0a741ff0-071b-4fb7-9820-574f67b2522a
-- title:
--   Auto: abs inv sin sub le
-- statement:
--   The Auto construction uses the abs inv sin sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1012-L1025
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1012-L1025

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real

theorem Auto.abs_inv_sin_sub_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |1 / Real.sin (π * s) - 1 / (π * s)| ≤ 1 := by sorry
