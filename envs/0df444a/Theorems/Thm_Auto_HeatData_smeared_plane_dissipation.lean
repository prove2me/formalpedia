-- Prove2me | Theorems.Thm_Auto_HeatData_smeared_plane_dissipation
-- name    : Auto.HeatData.smeared_plane_dissipation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:51:22.389739+00:00
-- url     : https://prove2.me/theorems/0ecf4f58-2601-4a4c-a568-60e708bb6413
-- title:
--   Heat Data: smeared plane dissipation
-- statement:
--   The Heat Data construction uses the smeared plane dissipation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5207-L5376
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5207-L5376

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
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ)

theorem Auto.HeatData.smeared_plane_dissipation (hh : 0 < Hd.h) (hη : 0 < η)
    (hα : ∀ k, α k = 1 ∨ α k = 11 / 10) (hsum : α 0 + α 1 + α 2 = 16 / 5) {sa sb : ℝ}
    (hsa : 0 < sa) (hab : sa ≤ sb) :
    (1 / 28) * ∫ s in sa..sb, ∑ v, Hd.Vbar α η v s ≤ Hd.Jbar α η sa - Hd.Jbar α η sb := by sorry
