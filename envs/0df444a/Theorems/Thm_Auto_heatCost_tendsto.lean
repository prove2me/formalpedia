-- Prove2me | Theorems.Thm_Auto_heatCost_tendsto
-- name    : Auto.heatCost_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:33.7318+00:00
-- url     : https://prove2.me/theorems/8cbd75b3-d26b-48aa-aef0-6d3bb9d1806e
-- title:
--   Auto: heat Cost tendsto
-- statement:
--   The Auto construction uses the heat Cost tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7075-L7085
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7075-L7085

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.heatCost_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ))
    {η : ℕ → ℝ} (hη0 : ∀ m, 0 < η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => ENNReal.ofReal (Hd.costDensity α (η m) z)) atTop
      (𝓝 (heatCost Hd α z)) := by sorry
