-- Prove2me | Theorems.Thm_Auto_lintegral_avgMeasure
-- name    : Auto.lintegral_avgMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:09.477625+00:00
-- url     : https://prove2.me/theorems/ca30e319-1b07-4b06-9111-ca28d7555d97
-- title:
--   Auto: lintegral avg Measure
-- statement:
--   The Auto construction uses the lintegral avg Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6419-L6424
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6419-L6424

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.lintegral_avgMeasure (s : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ d, F d ∂(avgMeasure s) = ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) * F d := by sorry
