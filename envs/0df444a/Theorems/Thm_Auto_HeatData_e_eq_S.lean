-- Prove2me | Theorems.Thm_Auto_HeatData_e_eq_S
-- name    : Auto.HeatData.e_eq_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:32:16.418029+00:00
-- url     : https://prove2.me/theorems/fe06027b-4cbf-4400-9ab5-ae85d59a11d8
-- title:
--   Heat Data: e eq S
-- statement:
--   The Heat Data construction uses the e eq S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3157-L3159
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3157-L3159

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

theorem Auto.HeatData.e_eq_S (η : ℝ) (v : Fin 3) : Hd.e p σ η v = energyReg η (Hd.S p σ v) := by sorry
