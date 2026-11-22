-- Prove2me | Theorems.Thm_Auto_det_shiftMat
-- name    : Auto.det_shiftMat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:45.309384+00:00
-- url     : https://prove2.me/theorems/8c770bb1-0ebc-4a7e-a718-742542129ea9
-- title:
--   Auto: det shift Mat
-- statement:
--   The Auto construction uses the det shift Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6665-L6667
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6665-L6667

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

theorem Auto.det_shiftMat (v : Fin 3) :
    (shiftMat v).det = 1 := by sorry
