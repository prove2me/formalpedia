-- Prove2me | Theorems.Thm_Auto_abs_sin_mul_div_le
-- name    : Auto.abs_sin_mul_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:53.012479+00:00
-- url     : https://prove2.me/theorems/43612ad7-6a01-4924-a48a-cc47a3917e18
-- title:
--   Auto: abs sin mul div le
-- statement:
--   The Auto construction uses the abs sin mul div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L359-L363
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L359-L363

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

theorem Auto.abs_sin_mul_div_le (v t : ℝ) : |Real.sin (v * t) / t| ≤ |v| := by sorry
