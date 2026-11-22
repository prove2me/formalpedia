-- Prove2me | Theorems.Thm_Auto_gaussianD_conv_gaussianD
-- name    : Auto.gaussianD_conv_gaussianD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:44.92761+00:00
-- url     : https://prove2.me/theorems/2555a07b-4c0a-4a77-985e-4779986c4670
-- title:
--   Auto: gaussian D conv gaussian D
-- statement:
--   The Auto construction uses the gaussian D conv gaussian D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L371-L397
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L371-L397

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

theorem Auto.gaussianD_conv_gaussianD (i j : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (t : ℝ) :
    ∫ d, gaussianD i σ (t - d) * gaussianD j τ d = gaussianD (i + j) (σ + τ) t := by sorry
