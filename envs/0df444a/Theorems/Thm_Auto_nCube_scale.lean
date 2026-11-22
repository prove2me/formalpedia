-- Prove2me | Theorems.Thm_Auto_nCube_scale
-- name    : Auto.nCube_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:51.661299+00:00
-- url     : https://prove2.me/theorems/0f3565d1-41fc-4b19-b0be-fd57498d5f18
-- title:
--   Auto: n Cube scale
-- statement:
--   The Auto construction uses the n Cube scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7349-L7355
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7349-L7355

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.nCube_scale {ι : Type*} [Fintype ι]
    (Hd : HeatData ι) (c : Fin 3 → ℂ) (v : Fin 3) :
    (scaleHeatData Hd c).nCube v = ‖c v‖ ^ 3 * Hd.nCube v := by sorry
