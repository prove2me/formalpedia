-- Prove2me | Theorems.Thm_Auto_HeatData_neighbor_cost_comparison
-- name    : Auto.HeatData.neighbor_cost_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:56.227746+00:00
-- url     : https://prove2.me/theorems/8e7f9526-3f6e-47e7-9c33-5a87ea3f621c
-- title:
--   Heat Data: neighbor cost comparison
-- statement:
--   The Heat Data construction uses the neighbor cost comparison property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3602-L3655
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3602-L3655

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

theorem Auto.HeatData.neighbor_cost_comparison (hh : 0 < Hd.h) {w : Fin 3} (hσ : 0 < σ w) {η : ℝ} (hη : 0 < η) :
    Hd.Yprev p σ η (w + 1) + Hd.Ynext p σ η (w - 1) ≤ √2 * Hd.V p σ η w := by sorry
