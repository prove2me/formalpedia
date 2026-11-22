-- Prove2me | Theorems.Thm_Auto_measurePreserving_carlesonCoord
-- name    : Auto.measurePreserving_carlesonCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:01:22.695529+00:00
-- url     : https://prove2.me/theorems/c591cc61-e35f-478c-9b24-c6aa6fd5013b
-- title:
--   Auto: measure Preserving carleson Coord
-- statement:
--   The Auto construction uses the measure Preserving carleson Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L254-L274
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L254-L274

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

theorem Auto.measurePreserving_carlesonCoord : MeasurePreserving carlesonCoord := by sorry
