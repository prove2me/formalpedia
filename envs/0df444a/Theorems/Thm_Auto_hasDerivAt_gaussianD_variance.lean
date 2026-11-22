-- Prove2me | Theorems.Thm_Auto_hasDerivAt_gaussianD_variance
-- name    : Auto.hasDerivAt_gaussianD_variance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:40.096818+00:00
-- url     : https://prove2.me/theorems/de604daf-9ad3-44e0-a13d-e74048ffdb3c
-- title:
--   Auto: has Deriv At gaussian D variance
-- statement:
--   The Auto construction uses the has Deriv At gaussian D variance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L215-L237
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L215-L237

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

theorem Auto.hasDerivAt_gaussianD_variance (j : ℕ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (fun τ => gaussianD j τ t) (gaussianD (j + 2) σ t / 2) σ := by sorry
