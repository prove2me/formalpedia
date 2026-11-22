-- Prove2me | Theorems.Thm_Auto_iteratedDeriv_gaussian_conv
-- name    : Auto.iteratedDeriv_gaussian_conv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:46.162222+00:00
-- url     : https://prove2.me/theorems/3f5b1b3c-ead5-4236-a735-589757723d7d
-- title:
--   Auto: iterated Deriv gaussian conv
-- statement:
--   The Auto construction uses the iterated Deriv gaussian conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L326-L334
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L326-L334

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

theorem Auto.iteratedDeriv_gaussian_conv (i : ℕ) {σ : ℝ} (hσ : 0 < σ) {G : ℝ → ℝ} (hG : Integrable G) :
    iteratedDeriv i (fun t => ∫ d, gaussian σ (t - d) * G d) = fun t => ∫ d, gaussianD i σ (t -
      d) * G d := by sorry
