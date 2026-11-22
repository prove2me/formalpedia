-- Prove2me | Theorems.Thm_Auto_HeatData_ddw_def
-- name    : Auto.HeatData.ddw_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:50.830747+00:00
-- url     : https://prove2.me/theorems/f089f2cd-f9ea-4c4c-bf21-63b28de2bde0
-- title:
--   Heat Data: ddw def
-- statement:
--   The Heat Data construction uses the ddw def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3169-L3169
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3169-L3169

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

theorem Auto.HeatData.ddw_def (v : Fin 3) : Hd.ddw p σ v = fun i => Hd.h * gaussianD 2 (σ v) (Hd.u i - p v) := by sorry
