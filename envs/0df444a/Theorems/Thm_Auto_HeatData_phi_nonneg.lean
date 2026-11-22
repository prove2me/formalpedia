-- Prove2me | Theorems.Thm_Auto_HeatData_phi_nonneg
-- name    : Auto.HeatData.phi_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:54.852814+00:00
-- url     : https://prove2.me/theorems/271bf6a9-78ca-48e7-9d76-78fe1d49068f
-- title:
--   Heat Data: phi nonneg
-- statement:
--   The Heat Data construction uses the phi nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4165-L4167
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4165-L4167

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
omit [Fintype ι] [DecidableEq ι]

theorem Auto.HeatData.phi_nonneg (b : ℝ) (v : Fin 3) (p : Fin 3 → ℝ) : 0 ≤ phi b v p := by sorry
