-- Prove2me | Theorems.Thm_Auto_isCompact_carlesonBox
-- name    : Auto.isCompact_carlesonBox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:21.105326+00:00
-- url     : https://prove2.me/theorems/34b46fe8-9561-492c-80e1-f49a4b029264
-- title:
--   Auto: is Compact carleson Box
-- statement:
--   The Auto construction uses the is Compact carleson Box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L207-L207
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L207-L207

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

theorem Auto.isCompact_carlesonBox (L : ℝ) : IsCompact (carlesonBox L) := by sorry
