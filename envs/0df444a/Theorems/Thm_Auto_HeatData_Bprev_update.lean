-- Prove2me | Theorems.Thm_Auto_HeatData_Bprev_update
-- name    : Auto.HeatData.Bprev_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:50.967655+00:00
-- url     : https://prove2.me/theorems/5a29ae5b-f99e-4e2b-869b-8e6c664d1cf9
-- title:
--   Heat Data: Bprev update
-- statement:
--   The Heat Data construction uses the Bprev update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3238-L3240
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3238-L3240

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

theorem Auto.HeatData.Bprev_update {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.Bprev (Function.update p k q) σ v = Hd.Bprev p σ v := by sorry
