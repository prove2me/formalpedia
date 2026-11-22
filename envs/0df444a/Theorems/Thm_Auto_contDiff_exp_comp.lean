-- Prove2me | Theorems.Thm_Auto_contDiff_exp_comp
-- name    : Auto.contDiff_exp_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:00.356288+00:00
-- url     : https://prove2.me/theorems/05ef0f3e-390a-4d57-8487-d02b84ec9a23
-- title:
--   Auto: cont Diff exp comp
-- statement:
--   The Auto construction uses the cont Diff exp comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L162-L164
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L162-L164

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

theorem Auto.contDiff_exp_comp {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => Complex.exp ((f p : ℂ) * Complex.I) := by sorry
