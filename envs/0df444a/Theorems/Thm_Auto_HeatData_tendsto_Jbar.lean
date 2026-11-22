-- Prove2me | Theorems.Thm_Auto_HeatData_tendsto_Jbar
-- name    : Auto.HeatData.tendsto_Jbar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:46.556453+00:00
-- url     : https://prove2.me/theorems/71f5ae80-6718-4a7e-90a1-2ebe471cb9d6
-- title:
--   Heat Data: tendsto Jbar
-- statement:
--   The Heat Data construction uses the tendsto Jbar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6016-L6103
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6016-L6103

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

theorem Auto.HeatData.tendsto_Jbar (hh : 0 < Hd.h) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2)
    {s : ℝ} (hs : 0 < s) {η : ℕ → ℝ} (hη0 : ∀ m, 0 < η m) (hη1 : ∀ m, η m ≤ 1)
    (hlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => Hd.Jbar α (η m) s) atTop (𝓝 (Hd.Jbar α 0 s)) := by sorry
