-- Prove2me | Theorems.Thm_Auto_HeatData_tr32_smul
-- name    : Auto.HeatData.tr32_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:00.583807+00:00
-- url     : https://prove2.me/theorems/09f1f6c8-054f-441d-90f0-48ec651a546f
-- title:
--   Heat Data: tr32 smul
-- statement:
--   The Heat Data construction uses the tr32 smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3677-L3679
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3677-L3679

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

theorem Auto.HeatData.tr32_smul (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K : Matrix κ κ ℂ) (c : ℝ) :
    tr32 η Γ ((c : ℂ) • K) = c * tr32 η Γ K := by sorry
