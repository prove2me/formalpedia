-- Prove2me | Theorems.Thm_Auto_eq_zero_of_nNorm_eq_zero
-- name    : Auto.eq_zero_of_nNorm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:14.289945+00:00
-- url     : https://prove2.me/theorems/f077b7ea-e92c-413c-b8c8-81aa39dd73c7
-- title:
--   Auto: eq zero of n Norm eq zero
-- statement:
--   The Auto construction uses the eq zero of n Norm eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6899-L6913
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6899-L6913

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

theorem Auto.eq_zero_of_nNorm_eq_zero {h : ℝ} (hh : 0 < h) {A : Matrix ι ι ℂ} (hA : nNorm h A = 0) :
    A = 0 := by sorry
