-- Prove2me | Theorems.Thm_Auto_sourceGaussian_support
-- name    : Auto.sourceGaussian_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:31.676526+00:00
-- url     : https://prove2.me/theorems/c0b521da-5852-4215-a272-b9fca4a966ae
-- title:
--   Auto: source Gaussian support
-- statement:
--   The Auto construction uses the source Gaussian support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7581-L7598
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7581-L7598

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.sourceGaussian_support (F : Fin 3 → ℝ × ℝ → ℂ) {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hF : ∀ v p, ρ < ‖p‖ → F v p = 0)
    (x : Fin 3 → ℝ) (hx : ρ < ‖x‖) :
    sourceGaussianIntegrand F a b x = 0 := by sorry
