-- Prove2me | Theorems.Thm_Auto_HeatData_Bnext_update
-- name    : Auto.HeatData.Bnext_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:10.82218+00:00
-- url     : https://prove2.me/theorems/013a514b-7723-4741-a368-c09c2ebb801b
-- title:
--   Heat Data: Bnext update
-- statement:
--   The Heat Data construction uses the Bnext update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3230-L3232
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3230-L3232

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

theorem Auto.HeatData.Bnext_update {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.Bnext (Function.update p k q) σ v = Hd.Bnext p σ v := by sorry
