-- Prove2me | Theorems.Thm_Auto_norm_carlesonMoll_le
-- name    : Auto.norm_carlesonMoll_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:02:11.203069+00:00
-- url     : https://prove2.me/theorems/c8785ca4-da8c-42c6-abba-b42fef64c36f
-- title:
--   Auto: norm carleson Moll le
-- statement:
--   The Auto construction uses the norm carleson Moll le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L576-L586
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean#L576-L586

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Auto.norm_carlesonMoll_le (k : ℕ) {h : ℝ → E} {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) (x : ℝ) :
    ‖carlesonMoll k h x‖ ≤ B := by sorry
