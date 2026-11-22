-- Prove2me | Theorems.Thm_Auto_continuous_carlesonW
-- name    : Auto.continuous_carlesonW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:38.822666+00:00
-- url     : https://prove2.me/theorems/a7801ee1-a3d2-4e4f-a6d4-eadfd7fe8c81
-- title:
--   Auto: continuous carleson W
-- statement:
--   The Auto construction uses the continuous carleson W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L62-L66
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L62-L66

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

theorem Auto.continuous_carlesonW : Continuous fun p : ℝ × ℝ => carlesonW p.1 p.2 := by sorry
