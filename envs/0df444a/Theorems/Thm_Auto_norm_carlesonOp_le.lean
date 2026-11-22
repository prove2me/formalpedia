-- Prove2me | Theorems.Thm_Auto_norm_carlesonOp_le
-- name    : Auto.norm_carlesonOp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:03:16.003638+00:00
-- url     : https://prove2.me/theorems/0557b37c-dea6-4ba0-9e5d-eedb524be65d
-- title:
--   Auto: norm carleson Op le
-- statement:
--   The Auto construction uses the norm carleson Op le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1169-L1181
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1169-L1181

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

theorem Auto.norm_carlesonOp_le {h : ℝ → ℂ} {ν : ℝ → ℝ} {B V : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
    (hV : ∀ x, |ν x| ≤ V) (x : ℝ) :
    ‖carlesonOp h ν x‖ ≤ B * V * ∫ t, carlesonWeight t := by sorry
