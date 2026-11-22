-- Prove2me | Theorems.Thm_Auto_norm_weight_sin_div_le
-- name    : Auto.norm_weight_sin_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:19.767212+00:00
-- url     : https://prove2.me/theorems/542376cf-1b99-4a57-a2dc-dd3cfa9812ca
-- title:
--   Auto: norm weight sin div le
-- statement:
--   The Auto construction uses the norm weight sin div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1031-L1035
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L1031-L1035

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

theorem Auto.norm_weight_sin_div_le (v t : ℝ) :
    ‖((carlesonWeight t * Real.sin (v * t) / t : ℝ) : ℂ)‖ ≤ |v| * carlesonWeight t := by sorry
