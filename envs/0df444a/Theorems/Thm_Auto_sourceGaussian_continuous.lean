-- Prove2me | Theorems.Thm_Auto_sourceGaussian_continuous
-- name    : Auto.sourceGaussian_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:12.736994+00:00
-- url     : https://prove2.me/theorems/5170c4b0-ca01-4e84-b983-c1dd6ba5efea
-- title:
--   Auto: source Gaussian continuous
-- statement:
--   The Auto construction uses the source Gaussian continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7574-L7579
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7574-L7579

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

theorem Auto.sourceGaussian_continuous (F : Fin 3 → ℝ × ℝ → ℂ)
    (hF : ∀ v, Continuous (F v)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Continuous (sourceGaussianIntegrand F a b) := by sorry
