-- Prove2me | Theorems.Thm_Auto_matCost_eq_iSup
-- name    : Auto.matCost_eq_iSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:44.334945+00:00
-- url     : https://prove2.me/theorems/aee90a15-32f5-405d-add9-b38696caf817
-- title:
--   Auto: mat Cost eq i Sup
-- statement:
--   The Auto construction uses the mat Cost eq i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6644-L6654
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6644-L6654

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

theorem Auto.matCost_eq_iSup {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ⨆ m : ℕ, matCost (P + ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) • 1) K := by sorry
