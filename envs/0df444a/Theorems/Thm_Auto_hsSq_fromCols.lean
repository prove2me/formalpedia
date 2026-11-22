-- Prove2me | Theorems.Thm_Auto_hsSq_fromCols
-- name    : Auto.hsSq_fromCols
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:57.770863+00:00
-- url     : https://prove2.me/theorems/004fc5dc-e870-43f2-8b55-cd13522670ab
-- title:
--   Auto: hs Sq from Cols
-- statement:
--   The Auto construction uses the hs Sq from Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5643-L5645
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5643-L5645

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

theorem Auto.hsSq_fromCols {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℂ) :
    hsSq (Matrix.fromCols A B) = hsSq A + hsSq B := by sorry
