-- Prove2me | Theorems.Thm_Auto_HeatData_rdiag_conjTranspose
-- name    : Auto.HeatData.rdiag_conjTranspose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:45.742599+00:00
-- url     : https://prove2.me/theorems/da71d1ef-99a3-46fa-9239-9bc506ed5648
-- title:
--   Heat Data: rdiag conj Transpose
-- statement:
--   The Heat Data construction uses the rdiag conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3105-L3105
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3105-L3105

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
omit [Fintype ι]

theorem Auto.HeatData.rdiag_conjTranspose (f : ι → ℝ) : (rdiag f)ᴴ = rdiag f := by sorry
