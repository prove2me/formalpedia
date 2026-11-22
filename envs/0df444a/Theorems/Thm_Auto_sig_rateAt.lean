-- Prove2me | Theorems.Thm_Auto_sig_rateAt
-- name    : Auto.sig_rateAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:13.863687+00:00
-- url     : https://prove2.me/theorems/6887dd24-eb06-435e-8248-81de78ae82d7
-- title:
--   Auto: sig rate At
-- statement:
--   The Auto construction uses the sig rate At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6855-L6859
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6855-L6859

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

theorem Auto.sig_rateAt (v : Fin 3) (s : ℝ) :
    HeatData.sig (rateAt v) s = Function.update (fun _ => 11 / 10 * s) v s := by sorry
