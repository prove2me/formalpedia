-- Prove2me | Theorems.Thm_Auto_HeatData_hasDerivAt_update_coord
-- name    : Auto.HeatData.hasDerivAt_update_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:28.231983+00:00
-- url     : https://prove2.me/theorems/f295223a-542d-47e7-bf23-e7d1c1416324
-- title:
--   Heat Data: has Deriv At update coord
-- statement:
--   The Heat Data construction uses the has Deriv At update coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3783-L3788
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3783-L3788

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

theorem Auto.HeatData.hasDerivAt_update_coord (σ : Fin 3 → ℝ) (k j : Fin 3) (x : ℝ) :
    HasDerivAt (fun τ => Function.update σ k τ j) ((Pi.single k (1 : ℝ) : Fin 3 → ℝ) j) x := by sorry
