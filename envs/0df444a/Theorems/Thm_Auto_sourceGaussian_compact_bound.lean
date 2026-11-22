-- Prove2me | Theorems.Thm_Auto_sourceGaussian_compact_bound
-- name    : Auto.sourceGaussian_compact_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:40.515099+00:00
-- url     : https://prove2.me/theorems/bd951b36-d656-4a1f-8262-f5ae65e4f3f9
-- title:
--   Auto: source Gaussian compact bound
-- statement:
--   The Auto construction uses the source Gaussian compact bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7600-L7633
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7600-L7633

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

theorem Auto.sourceGaussian_compact_bound (F : Fin 3 → ℝ × ℝ → ℂ)
    (hc : ∀ v, Continuous (F v)) (hs : ∀ v, HasCompactSupport (F v))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x, sourceGaussianIntegrand F a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (∫ p, ‖F v p‖ ^ 3) ^ (1 / 3 : ℝ) := by sorry
