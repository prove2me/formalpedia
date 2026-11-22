-- Prove2me | Theorems.Thm_Auto_HeatData_T_eq_DXD
-- name    : Auto.HeatData.T_eq_DXD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:08.376454+00:00
-- url     : https://prove2.me/theorems/65cc5318-2195-4c65-89c1-270f0c05d5f1
-- title:
--   Heat Data: T eq DXD
-- statement:
--   The Heat Data construction uses the T eq DXD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3692-L3701
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3692-L3701

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

theorem Auto.HeatData.T_eq_DXD (hh : 0 ≤ Hd.h) (v : Fin 3) :
    Hd.T p σ v = rdiag (Hd.dv p σ v) * Hd.X p σ v * rdiag (Hd.dv p σ v) := by sorry
