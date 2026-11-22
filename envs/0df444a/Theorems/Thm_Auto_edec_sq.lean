-- Prove2me | Theorems.Thm_Auto_edec_sq
-- name    : Auto.edec_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:55.829406+00:00
-- url     : https://prove2.me/theorems/5d3dd66b-5716-44b4-8cc4-4f07cee9c826
-- title:
--   Auto: edec sq
-- statement:
--   The Auto construction uses the edec sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4092-L4094
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4092-L4094

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
open Auto
noncomputable section

theorem Auto.edec_sq {b : ℝ} (x : ℝ) :
    edec b x ^ 2 = Real.exp (-(x ^ 2) / (8 * b)) := by sorry
