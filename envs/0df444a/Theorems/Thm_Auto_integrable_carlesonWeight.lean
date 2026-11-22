-- Prove2me | Theorems.Thm_Auto_integrable_carlesonWeight
-- name    : Auto.integrable_carlesonWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:15.286185+00:00
-- url     : https://prove2.me/theorems/35428286-b1ce-4e0a-9aa0-a071fe757a36
-- title:
--   Auto: integrable carleson Weight
-- statement:
--   The Auto construction uses the integrable carleson Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L134-L139
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L134-L139

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

theorem Auto.integrable_carlesonWeight : Integrable carlesonWeight := by sorry
