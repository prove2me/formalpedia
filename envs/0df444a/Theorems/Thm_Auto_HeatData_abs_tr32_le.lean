-- Prove2me | Theorems.Thm_Auto_HeatData_abs_tr32_le
-- name    : Auto.HeatData.abs_tr32_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:49:22.532841+00:00
-- url     : https://prove2.me/theorems/b871eed8-9647-41e7-9f3b-b5666821b059
-- title:
--   Heat Data: abs tr32 le
-- statement:
--   The Heat Data construction uses the abs tr32 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4352-L4364
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4352-L4364

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Auto.HeatData.abs_tr32_le {Γ : Matrix κ κ ℂ} (hΓ : Γ.PosSemidef) {η : ℝ} (hη : 0 ≤ η)
    (K : Matrix κ κ ℂ) :
    |HeatData.tr32 η Γ K| ≤ (3 / 2) * √(Γ.trace.re + Fintype.card κ * η) * √(hsSq K) := by sorry
