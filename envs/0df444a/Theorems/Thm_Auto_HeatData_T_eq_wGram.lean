-- Prove2me | Theorems.Thm_Auto_HeatData_T_eq_wGram
-- name    : Auto.HeatData.T_eq_wGram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:40.63623+00:00
-- url     : https://prove2.me/theorems/eb38ddae-b3c1-4772-a0df-459d3a3add24
-- title:
--   Heat Data: T eq w Gram
-- statement:
--   The Heat Data construction uses the T eq w Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3121-L3124
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3121-L3124

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)

theorem Auto.HeatData.T_eq_wGram (hh : 0 ≤ Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.T p σ v = wGram (Hd.Brow p σ v) (Hd.w p σ v) := by sorry
