-- Prove2me | Theorems.Thm_Auto_gaussian_conv_gaussian
-- name    : Auto.gaussian_conv_gaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:50.057858+00:00
-- url     : https://prove2.me/theorems/4f4f13fc-9f9e-4923-9a12-9c787ca782d9
-- title:
--   Auto: gaussian conv gaussian
-- statement:
--   The Auto construction uses the gaussian conv gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L336-L369
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L336-L369

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

theorem Auto.gaussian_conv_gaussian {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (t : ℝ) :
    ∫ d, gaussian σ (t - d) * gaussian τ d = gaussian (σ + τ) t := by sorry
