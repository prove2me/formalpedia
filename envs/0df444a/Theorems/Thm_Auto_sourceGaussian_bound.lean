-- Prove2me | Theorems.Thm_Auto_sourceGaussian_bound
-- name    : Auto.sourceGaussian_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:59.990251+00:00
-- url     : https://prove2.me/theorems/ea9475a0-9675-4610-913c-cca28eb675af
-- title:
--   Auto: source Gaussian bound
-- statement:
--   The Auto construction uses the source Gaussian bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7666-L7709
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7666-L7709

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

theorem Auto.sourceGaussian_bound (F : Fin 3 → ℝ × ℝ → ℂ)
    (hc : ∀ v, Continuous (F v)) (hL : ∀ v, MemLp (F v) 3)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hi : Integrable (sourceGaussianIntegrand F a b)) :
    ‖∫ x, sourceGaussianIntegrand F a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (eLpNorm (F v) 3).toReal := by sorry
