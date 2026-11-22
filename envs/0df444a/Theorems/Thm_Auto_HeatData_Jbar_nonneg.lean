-- Prove2me | Theorems.Thm_Auto_HeatData_Jbar_nonneg
-- name    : Auto.HeatData.Jbar_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:42.381977+00:00
-- url     : https://prove2.me/theorems/c87073e7-01ba-401f-bbd8-d04da49b92b4
-- title:
--   Heat Data: Jbar nonneg
-- statement:
--   The Heat Data construction uses the Jbar nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5999-L6002
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5999-L6002

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

theorem Auto.HeatData.Jbar_nonneg (α : Fin 3 → ℝ) {η : ℝ} (hη : 0 ≤ η) (s : ℝ) : 0 ≤ Hd.Jbar α η s := by sorry
