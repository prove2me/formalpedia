-- Prove2me | Theorems.Thm_Auto_HeatData_dw_def
-- name    : Auto.HeatData.dw_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:20.932847+00:00
-- url     : https://prove2.me/theorems/f3888ef6-0bfc-4375-ba2b-5e3ce594fb3c
-- title:
--   Heat Data: dw def
-- statement:
--   The Heat Data construction uses the dw def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3166-L3166
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3166-L3166

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
omit [Fintype ι] [DecidableEq ι]

theorem Auto.HeatData.dw_def (v : Fin 3) : Hd.dw p σ v = fun i => -(Hd.h * gaussianD 1 (σ v) (Hd.u i - p v)) := by sorry
