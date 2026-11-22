-- Prove2me | Theorems.Thm_Auto_inv_sin_sub_inv_le
-- name    : Auto.inv_sin_sub_inv_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:56.218334+00:00
-- url     : https://prove2.me/theorems/181be0c2-f3d3-4389-8490-4415e1f48426
-- title:
--   Auto: inv sin sub inv le
-- statement:
--   The Auto construction uses the inv sin sub inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L993-L1010
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L993-L1010

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

theorem Auto.inv_sin_sub_inv_le {y : ℝ} (hy : 0 < y) (hy' : y ≤ π / 2) :
    0 ≤ 1 / Real.sin y - 1 / y ∧ 1 / Real.sin y - 1 / y ≤ 1 := by sorry
