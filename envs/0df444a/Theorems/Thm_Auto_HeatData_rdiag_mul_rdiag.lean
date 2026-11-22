-- Prove2me | Theorems.Thm_Auto_HeatData_rdiag_mul_rdiag
-- name    : Auto.HeatData.rdiag_mul_rdiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:39.540824+00:00
-- url     : https://prove2.me/theorems/04d7ab24-eac0-4138-872f-3c74a019631f
-- title:
--   Heat Data: rdiag mul rdiag
-- statement:
--   The Heat Data construction uses the rdiag mul rdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3100-L3102
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3100-L3102

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

theorem Auto.HeatData.rdiag_mul_rdiag (f g : ι → ℝ) :
    rdiag f * rdiag g = rdiag (f * g) := by sorry
