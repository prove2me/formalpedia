-- Prove2me | Theorems.Thm_Auto_HeatData_weight_bounds
-- name    : Auto.HeatData.weight_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:55.484851+00:00
-- url     : https://prove2.me/theorems/c1d477e2-8293-413c-9ade-5f2c49eda3b8
-- title:
--   Heat Data: weight bounds
-- statement:
--   The Heat Data construction uses the weight bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4170-L4201
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4170-L4201

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
variable (Hd : HeatData ι)
omit [DecidableEq ι] [Fintype ι]

theorem Auto.HeatData.weight_bounds [Finite ι] (hh : 0 ≤ Hd.h) {σa σb : ℝ} (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ k i, |Hd.w p σ k i| ≤ C *
      edec σb (p k) ^ 2 ∧ |Hd.dw p σ k i| ≤ C * edec σb (p k) ^ 2 ∧ |Hd.ddw p σ k i| ≤ C * edec σb
      (p k) ^ 2 ∧ Hd.sqw p σ k i ≤ √C * edec σb (p k) := by sorry
