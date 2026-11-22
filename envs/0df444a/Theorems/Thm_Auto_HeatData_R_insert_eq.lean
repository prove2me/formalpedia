-- Prove2me | Theorems.Thm_Auto_HeatData_R_insert_eq
-- name    : Auto.HeatData.R_insert_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:34.624617+00:00
-- url     : https://prove2.me/theorems/effd2abb-ee58-43c9-974f-76c00e780a92
-- title:
--   Heat Data: R insert eq
-- statement:
--   The Heat Data construction uses the R insert eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6497-L6505
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6497-L6505

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)

theorem Auto.HeatData.R_insert_eq (hh : 0 ≤ Hd.h) (p σ : Fin 3 → ℝ) (v : Fin 3) (D : ι → ℝ) (hσ : 0 < σ v) :
    (Hd.R p σ v)ᴴ * rdiag D * Hd.R p σ v = wGram (Hd.Brow p σ v) (fun i => Hd.w p σ v i * D i) := by sorry
