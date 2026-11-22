-- Prove2me | Theorems.Thm_Auto_dexp_cases
-- name    : Auto.dexp_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:02.338851+00:00
-- url     : https://prove2.me/theorems/e82a63e6-d1ed-43b5-ab7c-cf10907b9aa5
-- title:
--   Auto: dexp cases
-- statement:
--   The Auto construction uses the dexp cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6861-L6863
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6861-L6863

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

theorem Auto.dexp_cases (m : ℕ) (v : Fin 3) :
    dexp m v = 1 ∨ dexp m v = 2 := by sorry
