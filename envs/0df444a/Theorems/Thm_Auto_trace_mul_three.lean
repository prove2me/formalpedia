-- Prove2me | Theorems.Thm_Auto_trace_mul_three
-- name    : Auto.trace_mul_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:00.140661+00:00
-- url     : https://prove2.me/theorems/da2e5440-0841-40ea-be76-090d6cf2bb10
-- title:
--   Auto: trace mul three
-- statement:
--   The Auto construction uses the trace mul three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6264-L6267
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6264-L6267

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
omit [DecidableEq ι]

theorem Auto.trace_mul_three (X Y Z : Matrix ι ι ℂ) :
    (X * Y * Z).trace = ∑ i, ∑ j, ∑ k, X i j * Y j k * Z k i := by sorry
