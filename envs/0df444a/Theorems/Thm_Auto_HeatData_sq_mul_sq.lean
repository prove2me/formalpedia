-- Prove2me | Theorems.Thm_Auto_HeatData_sq_mul_sq
-- name    : Auto.HeatData.sq_mul_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:33.467812+00:00
-- url     : https://prove2.me/theorems/5767f492-a55a-4705-aea1-3bfbfa19bf8d
-- title:
--   Heat Data: sq mul sq
-- statement:
--   The Heat Data construction uses the sq mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3108-L3112
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3108-L3112

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

theorem Auto.HeatData.sq_mul_sq (hh : 0 ≤ Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    Hd.sqw p σ v * Hd.sqw p σ v = Hd.w p σ v := by sorry
