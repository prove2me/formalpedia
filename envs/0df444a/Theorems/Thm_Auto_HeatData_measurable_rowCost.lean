-- Prove2me | Theorems.Thm_Auto_HeatData_measurable_rowCost
-- name    : Auto.HeatData.measurable_rowCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:59.514922+00:00
-- url     : https://prove2.me/theorems/349b7ef5-6cb8-496e-bb08-48423b9564f0
-- title:
--   Heat Data: measurable row Cost
-- statement:
--   The Heat Data construction uses the measurable row Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6825-L6838
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6825-L6838

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

theorem Auto.HeatData.measurable_rowCost (σ : Fin 3 → ℝ) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    Measurable fun p : Fin 3 → ℝ => matCost (Hd.T p σ v) (Hd.Ui p σ v) := by sorry
