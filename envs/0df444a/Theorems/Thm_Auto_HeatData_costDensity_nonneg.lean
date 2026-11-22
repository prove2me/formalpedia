-- Prove2me | Theorems.Thm_Auto_HeatData_costDensity_nonneg
-- name    : Auto.HeatData.costDensity_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:49.532129+00:00
-- url     : https://prove2.me/theorems/1bcdd688-4e28-48fa-b099-0f6efa9c41b7
-- title:
--   Heat Data: cost Density nonneg
-- statement:
--   The Heat Data construction uses the cost Density nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6131-L6134
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6131-L6134

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

theorem Auto.HeatData.costDensity_nonneg (α : Fin 3 → ℝ) (η : ℝ) (z : ℝ × (Fin 3 → ℝ)) :
    0 ≤ Hd.costDensity α η z := by sorry
