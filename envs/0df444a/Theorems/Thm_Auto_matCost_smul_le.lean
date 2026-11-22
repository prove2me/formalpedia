-- Prove2me | Theorems.Thm_Auto_matCost_smul_le
-- name    : Auto.matCost_smul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:19.893847+00:00
-- url     : https://prove2.me/theorems/45795d7f-1a01-4f8d-96ab-12bf7f15f6b0
-- title:
--   Auto: mat Cost smul le
-- statement:
--   The Auto construction uses the mat Cost smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6426-L6441
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6426-L6441

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

theorem Auto.matCost_smul_le {n : Type*} [Fintype n] [DecidableEq n] (P K : Matrix n n ℂ) (c : ℝ) :
    matCost P ((c : ℂ) • K) ≤ ENNReal.ofReal (c ^ 2) * matCost P K := by sorry
