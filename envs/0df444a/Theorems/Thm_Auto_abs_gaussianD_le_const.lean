-- Prove2me | Theorems.Thm_Auto_abs_gaussianD_le_const
-- name    : Auto.abs_gaussianD_le_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:08.74461+00:00
-- url     : https://prove2.me/theorems/3be4e164-3f20-422e-84e8-d2765e78286f
-- title:
--   Auto: abs gaussian D le const
-- statement:
--   The Auto construction uses the abs gaussian D le const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L283-L295
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L283-L295

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
open Real

theorem Auto.abs_gaussianD_le_const (j : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ M : ℝ, ∀ t, |gaussianD j σ t| ≤ M := by sorry
