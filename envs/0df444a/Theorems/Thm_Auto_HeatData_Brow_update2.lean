-- Prove2me | Theorems.Thm_Auto_HeatData_Brow_update2
-- name    : Auto.HeatData.Brow_update2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:20.257902+00:00
-- url     : https://prove2.me/theorems/371756c0-030e-4d8d-8a22-958af5096f38
-- title:
--   Heat Data: Brow update2
-- statement:
--   The Heat Data construction uses the Brow update2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6487-L6489
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6487-L6489

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
open Auto.HeatData
variable (Hd : HeatData ι)

theorem Auto.HeatData.Brow_update2 (p σ : Fin 3 → ℝ) (v : Fin 3) (q τ : ℝ) :
    Hd.Brow (Function.update p v q) (Function.update σ v τ) v = Hd.Brow p σ v := by sorry
