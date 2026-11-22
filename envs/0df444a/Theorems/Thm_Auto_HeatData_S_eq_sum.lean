-- Prove2me | Theorems.Thm_Auto_HeatData_S_eq_sum
-- name    : Auto.HeatData.S_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:44.345018+00:00
-- url     : https://prove2.me/theorems/f590b1f6-1fd5-4626-b46b-b2ff66d94e46
-- title:
--   Heat Data: S eq sum
-- statement:
--   The Heat Data construction uses the S eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3570-L3573
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3570-L3573

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

theorem Auto.HeatData.S_eq_sum (v : Fin 3) :
    Hd.S p σ v = Hd.W p σ v * (Hd.W p σ v)ᴴ + (Hd.W p σ (v - 1))ᴴ * Hd.W p σ (v - 1) := by sorry
