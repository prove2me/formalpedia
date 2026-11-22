-- Prove2me | Theorems.Thm_Auto_HeatData_S_eq_wGram
-- name    : Auto.HeatData.S_eq_wGram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:02.829609+00:00
-- url     : https://prove2.me/theorems/9e65ad65-f0d5-47cd-94bf-76c56f556462
-- title:
--   Heat Data: S eq w Gram
-- statement:
--   The Heat Data construction uses the S eq w Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3126-L3155
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3126-L3155

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

theorem Auto.HeatData.S_eq_wGram (hh : 0 ≤ Hd.h) {v : Fin 3} (hσ1 : 0 < σ (v + 1)) (hσ2 : 0 < σ (v - 1)) :
    Hd.S p σ v = wGram (Hd.Bnext p σ v) (Hd.w p σ (v + 1)) + wGram (Hd.Bprev p σ v) (Hd.w p σ (v
      - 1)) := by sorry
