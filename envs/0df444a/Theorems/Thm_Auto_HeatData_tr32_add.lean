-- Prove2me | Theorems.Thm_Auto_HeatData_tr32_add
-- name    : Auto.HeatData.tr32_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:01.741143+00:00
-- url     : https://prove2.me/theorems/9755afb7-5df2-4ae5-99f6-4eb4ca8bee41
-- title:
--   Heat Data: tr32 add
-- statement:
--   The Heat Data construction uses the tr32 add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3673-L3675
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3673-L3675

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

theorem Auto.HeatData.tr32_add (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K L : Matrix κ κ ℂ) :
    tr32 η Γ (K + L) = tr32 η Γ K + tr32 η Γ L := by sorry
