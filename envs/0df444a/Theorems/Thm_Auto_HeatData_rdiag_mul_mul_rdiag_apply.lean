-- Prove2me | Theorems.Thm_Auto_HeatData_rdiag_mul_mul_rdiag_apply
-- name    : Auto.HeatData.rdiag_mul_mul_rdiag_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:21.021816+00:00
-- url     : https://prove2.me/theorems/df21dd68-73aa-4b06-a44c-622ed3c0fde3
-- title:
--   Heat Data: rdiag mul mul rdiag apply
-- statement:
--   The Heat Data construction uses the rdiag mul mul rdiag apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3703-L3706
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3703-L3706

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)

theorem Auto.HeatData.rdiag_mul_mul_rdiag_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (d d' : κ → ℝ)
    (M : Matrix κ κ ℂ) (a b : κ) :
    (rdiag d * M * rdiag d') a b = (d a : ℂ) * M a b * (d' b : ℂ) := by sorry
