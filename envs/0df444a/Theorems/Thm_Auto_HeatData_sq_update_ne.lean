-- Prove2me | Theorems.Thm_Auto_HeatData_sq_update_ne
-- name    : Auto.HeatData.sq_update_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:50.862129+00:00
-- url     : https://prove2.me/theorems/6779a637-f4c9-4d62-b1cd-bc88429ab49f
-- title:
--   Heat Data: sq update ne
-- statement:
--   The Heat Data construction uses the sq update ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3213-L3215
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3213-L3215

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

theorem Auto.HeatData.sq_update_ne {v k : Fin 3} (hk : k ≠ v) (q : ℝ) :
    Hd.sqw (Function.update p v q) σ k = Hd.sqw p σ k := by sorry
