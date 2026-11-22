-- Prove2me | Theorems.Thm_Auto_HeatData_costDensity_integrable
-- name    : Auto.HeatData.costDensity_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:25:53.113812+00:00
-- url     : https://prove2.me/theorems/9b4cf107-a38b-4c7d-b0ab-98fbbf0d653f
-- title:
--   Heat Data: cost Density integrable
-- statement:
--   The Heat Data construction uses the cost Density integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6120-L6129
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6120-L6129

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

theorem Auto.HeatData.costDensity_integrable (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ}
    (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    Integrable (Hd.costDensity α η) ((volume.restrict (Set.Ioc ta tb)).prod volume) := by sorry
