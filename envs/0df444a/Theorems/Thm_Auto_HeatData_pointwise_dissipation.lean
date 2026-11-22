-- Prove2me | Theorems.Thm_Auto_HeatData_pointwise_dissipation
-- name    : Auto.HeatData.pointwise_dissipation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:22.099285+00:00
-- url     : https://prove2.me/theorems/563f889d-f4ed-4632-920e-26c7bb9f30b4
-- title:
--   Heat Data: pointwise dissipation
-- statement:
--   The Heat Data construction uses the pointwise dissipation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5145-L5189
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5145-L5189

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
variable (Hd : HeatData ι)

theorem Auto.HeatData.pointwise_dissipation (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) (p σ : Fin 3 → ℝ)
    (hσ : ∀ k, 0 < σ k) {α : Fin 3 → ℝ} (hα : ∀ k, α k = 1 ∨ α k = 11 / 10)
    (hsum : α 0 + α 1 + α 2 = 16 / 5) :
    ∑ v, (33 / 20 * Hd.Z p σ η v - (α v * Hd.V p σ η v + α (v + 1) * Hd.Ynext p σ η v + α (v -
      1) * Hd.Yprev p σ η v) / 2) ≤ -(1 / 28) * ∑ v, Hd.V p σ η v := by sorry
