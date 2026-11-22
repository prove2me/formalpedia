-- Prove2me | Theorems.Thm_Auto_rateAt_cases
-- name    : Auto.rateAt_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:03.571643+00:00
-- url     : https://prove2.me/theorems/33a87212-4c7a-4087-a5b8-06c619e2a98d
-- title:
--   Auto: rate At cases
-- statement:
--   The Auto construction uses the rate At cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6848-L6849
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6848-L6849

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

theorem Auto.rateAt_cases (v : Fin 3) : ∀ k, rateAt v k = 1 ∨ rateAt v k = 11 / 10 := by sorry
