-- Prove2me | Theorems.Thm_Auto_HeatData_R_eq
-- name    : Auto.HeatData.R_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:23:21.016369+00:00
-- url     : https://prove2.me/theorems/74e2e268-c0cf-4bac-9b00-79c30bee3b12
-- title:
--   Heat Data: R eq
-- statement:
--   The Heat Data construction uses the R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3114-L3119
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3114-L3119

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

theorem Auto.HeatData.R_eq (v : Fin 3) :
    Hd.R p σ v = rdiag (Hd.sqw p σ v) * rowMat (Hd.A v) (Hd.A (v - 1)) * Hd.Dc p σ v := by sorry
