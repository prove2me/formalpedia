-- Prove2me | Theorems.Thm_Auto_heatCost_aemeasurable
-- name    : Auto.heatCost_aemeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:28.790233+00:00
-- url     : https://prove2.me/theorems/808a1b87-9199-48f4-8f07-5e26131acf25
-- title:
--   Auto: heat Cost aemeasurable
-- statement:
--   The Auto construction uses the heat Cost aemeasurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7087-L7098
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7087-L7098

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

theorem Auto.heatCost_aemeasurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {α : Fin 3 → ℝ}
    (hα1 : ∀ v, 1 ≤ α v) (hα2 : ∀ v, α v ≤ 2)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    AEMeasurable (heatCost Hd α) ((volume.restrict (Set.Ioc a b)).prod volume) := by sorry
