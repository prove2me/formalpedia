-- Prove2me | Theorems.Thm_Auto_HeatData_fin3_ne_pred
-- name    : Auto.HeatData.fin3_ne_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:46.691025+00:00
-- url     : https://prove2.me/theorems/867cd57e-ff86-4003-a82b-e3f6ce2450f9
-- title:
--   Heat Data: fin3 ne pred
-- statement:
--   The Heat Data construction uses the fin3 ne pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3188-L3188
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3188-L3188

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

theorem Auto.HeatData.fin3_ne_pred (v : Fin 3) : v ≠ v - 1 := by sorry
