-- Prove2me | Theorems.Thm_Auto_sourceGaussianPairing_comp
-- name    : Auto.sourceGaussianPairing_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:13.50698+00:00
-- url     : https://prove2.me/theorems/75f085eb-b0c6-4dd0-9460-ca6ca091bbc6
-- title:
--   Auto: source Gaussian Pairing comp
-- statement:
--   The Auto construction uses the source Gaussian Pairing comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8398-L8412
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8398-L8412

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

theorem Auto.sourceGaussianPairing_comp (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (q : (ℝ × ℝ) × ℝ) :
    sourceGaussianPairing F a b (triangularSpaceEquiv q) =
      -(F 0 q.1 * triangularShiftProduct (triangularPullback₁ (F 1))
        (triangularPullback₂ (F 2)) q.1 q.2 * (Kern 3 a b q.2 : ℂ)) := by sorry
