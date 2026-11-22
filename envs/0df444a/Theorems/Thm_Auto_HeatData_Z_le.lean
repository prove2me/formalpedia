-- Prove2me | Theorems.Thm_Auto_HeatData_Z_le
-- name    : Auto.HeatData.Z_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:16.096562+00:00
-- url     : https://prove2.me/theorems/578928fa-75e4-4545-9ba3-69d5615fa31c
-- title:
--   Heat Data: Z le
-- statement:
--   The Heat Data construction uses the Z le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5132-L5141
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5132-L5141

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
variable (Hd : HeatData ι)

theorem Auto.HeatData.Z_le (p σ : Fin 3 → ℝ) {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    Hd.Z p σ η v ≤ (Hd.Ynext p σ η v + Hd.Yprev p σ η v) / 2 := by sorry
