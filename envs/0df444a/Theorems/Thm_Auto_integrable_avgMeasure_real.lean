-- Prove2me | Theorems.Thm_Auto_integrable_avgMeasure_real
-- name    : Auto.integrable_avgMeasure_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:12.655358+00:00
-- url     : https://prove2.me/theorems/1f4efc87-0969-4e57-ae57-b4c427759c2c
-- title:
--   Auto: integrable avg Measure real
-- statement:
--   The Auto construction uses the integrable avg Measure real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6455-L6460
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6455-L6460

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

theorem Auto.integrable_avgMeasure_real (s : ℝ) {f : ℝ → ℝ}
    (hf : Integrable (fun d => gaussian (1 / 10 * s) d * f d)) :
    Integrable f (avgMeasure s) := by sorry
