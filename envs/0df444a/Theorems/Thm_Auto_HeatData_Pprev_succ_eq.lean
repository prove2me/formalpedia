-- Prove2me | Theorems.Thm_Auto_HeatData_Pprev_succ_eq
-- name    : Auto.HeatData.Pprev_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:40.449038+00:00
-- url     : https://prove2.me/theorems/0afe8b8f-d4e2-466b-8af9-a396c8592472
-- title:
--   Heat Data: Pprev succ eq
-- statement:
--   The Heat Data construction uses the Pprev succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3557-L3561
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3557-L3561

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

theorem Auto.HeatData.Pprev_succ_eq (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.Pprev p σ (v + 1) = (Hd.W p σ v)ᴴ * Hd.N p σ v * Hd.W p σ v := by sorry
