-- Prove2me | Theorems.Thm_Auto_HeatData_Mrow_eq
-- name    : Auto.HeatData.Mrow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:12.739101+00:00
-- url     : https://prove2.me/theorems/f6eb413b-c819-499c-8c4a-ebfcb705fc1a
-- title:
--   Heat Data: Mrow eq
-- statement:
--   The Heat Data construction uses the Mrow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3721-L3725
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3721-L3725

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

theorem Auto.HeatData.Mrow_eq (v : Fin 3) :
    Hd.Mrow p σ v = rdiag (Hd.dv p σ v) * wGram (rowMat (Hd.A v) (Hd.A (v - 1))) (fun i =>
      Hd.ddw p σ v i / 2) * rdiag (Hd.dv p σ v) := by sorry
