-- Prove2me | Theorems.Thm_Auto_rateAt_sum
-- name    : Auto.rateAt_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:07.64905+00:00
-- url     : https://prove2.me/theorems/29703b62-04ce-4c6a-91e1-380dc4c61630
-- title:
--   Auto: rate At sum
-- statement:
--   The Auto construction uses the rate At sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6851-L6853
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6851-L6853

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

theorem Auto.rateAt_sum (v : Fin 3) :
    rateAt v 0 + rateAt v 1 + rateAt v 2 = 16 / 5 := by sorry
