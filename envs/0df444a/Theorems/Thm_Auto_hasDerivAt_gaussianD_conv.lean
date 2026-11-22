-- Prove2me | Theorems.Thm_Auto_hasDerivAt_gaussianD_conv
-- name    : Auto.hasDerivAt_gaussianD_conv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:39:56.158555+00:00
-- url     : https://prove2.me/theorems/11b19e0c-594b-4276-9a3b-b4e8b7192e0e
-- title:
--   Auto: has Deriv At gaussian D conv
-- statement:
--   The Auto construction uses the has Deriv At gaussian D conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L297-L324
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L297-L324

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

theorem Auto.hasDerivAt_gaussianD_conv (i : ℕ) {σ : ℝ} (hσ : 0 < σ) {G : ℝ → ℝ} (hG : Integrable G)
    (t : ℝ) :
    HasDerivAt (fun t => ∫ d, gaussianD i σ (t - d) * G d) (∫ d, gaussianD (i + 1) σ (t - d) * G
      d) t := by sorry
