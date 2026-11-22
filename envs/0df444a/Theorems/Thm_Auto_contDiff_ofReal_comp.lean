-- Prove2me | Theorems.Thm_Auto_contDiff_ofReal_comp
-- name    : Auto.contDiff_ofReal_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:31.978806+00:00
-- url     : https://prove2.me/theorems/72838611-512f-4052-a046-f1672ce5820d
-- title:
--   Auto: cont Diff of Real comp
-- statement:
--   The Auto construction uses the cont Diff of Real comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L158-L160
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L158-L160

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

theorem Auto.contDiff_ofReal_comp {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => (f p : ℂ) := by sorry
