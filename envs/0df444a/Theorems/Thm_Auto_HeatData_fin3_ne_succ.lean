-- Prove2me | Theorems.Thm_Auto_HeatData_fin3_ne_succ
-- name    : Auto.HeatData.fin3_ne_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:33.860802+00:00
-- url     : https://prove2.me/theorems/a82972ca-ea35-42a7-939c-e3a43b36c6fd
-- title:
--   Heat Data: fin3 ne succ
-- statement:
--   The Heat Data construction uses the fin3 ne succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3186-L3186
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3186-L3186

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

theorem Auto.HeatData.fin3_ne_succ (v : Fin 3) : v ≠ v + 1 := by sorry
