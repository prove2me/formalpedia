-- Prove2me | Theorems.Thm_Auto_sourceGaussian_integral_eq
-- name    : Auto.sourceGaussian_integral_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:58:18.498786+00:00
-- url     : https://prove2.me/theorems/f5e8fd70-b7b9-45e0-ab4c-2c5a216991fc
-- title:
--   Auto: source Gaussian integral eq
-- statement:
--   The Auto construction uses the source Gaussian integral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8426-L8438
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8426-L8438

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

theorem Auto.sourceGaussian_integral_eq (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, sourceGaussianIntegrand (fun v => F v) a b x) =
      -(∫ q : (ℝ × ℝ) × ℝ, F 0 q.1 *
        triangularShiftProduct (triangularPullback₁ (F 1)) (triangularPullback₂ (F 2))
          q.1 q.2 * (Kern 3 a b q.2 : ℂ)) := by sorry
