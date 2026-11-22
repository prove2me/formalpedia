-- Prove2me | Theorems.Thm_Auto_measurable_carlesonWeight
-- name    : Auto.measurable_carlesonWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:25:27.662633+00:00
-- url     : https://prove2.me/theorems/802c47fa-d26a-4e59-9354-b16968e8c674
-- title:
--   Auto: measurable carleson Weight
-- statement:
--   The Auto construction uses the measurable carleson Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L130-L132
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L130-L132

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

theorem Auto.measurable_carlesonWeight : Measurable carlesonWeight := by sorry
