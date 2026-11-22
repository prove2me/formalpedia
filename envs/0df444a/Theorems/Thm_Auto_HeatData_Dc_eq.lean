-- Prove2me | Theorems.Thm_Auto_HeatData_Dc_eq
-- name    : Auto.HeatData.Dc_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:18.875325+00:00
-- url     : https://prove2.me/theorems/776733e1-a479-482f-b041-d762e46cceb5
-- title:
--   Heat Data: Dc eq
-- statement:
--   The Heat Data construction uses the Dc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3688-L3690
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3688-L3690

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
omit [Fintype ι]

theorem Auto.HeatData.Dc_eq (v : Fin 3) : Hd.Dc p σ v = rdiag (Hd.dv p σ v) := by sorry
