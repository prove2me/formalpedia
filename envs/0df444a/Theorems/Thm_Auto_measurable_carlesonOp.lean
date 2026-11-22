-- Prove2me | Theorems.Thm_Auto_measurable_carlesonOp
-- name    : Auto.measurable_carlesonOp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:03:17.71111+00:00
-- url     : https://prove2.me/theorems/8b6fb901-c6db-4d2e-a83f-20ec4365120f
-- title:
--   Auto: measurable carleson Op
-- statement:
--   The Auto construction uses the measurable carleson Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1161-L1167
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1161-L1167

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

theorem Auto.measurable_carlesonOp {h : ℝ → ℂ} {ν : ℝ → ℝ} (hh : Measurable h) (hν : Measurable ν) :
    Measurable (carlesonOp h ν) := by sorry
