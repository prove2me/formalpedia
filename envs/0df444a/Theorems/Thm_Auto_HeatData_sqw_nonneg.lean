-- Prove2me | Theorems.Thm_Auto_HeatData_sqw_nonneg
-- name    : Auto.HeatData.sqw_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:49:02.773443+00:00
-- url     : https://prove2.me/theorems/faf20b2b-1244-4413-97ad-f9a6a8df2132
-- title:
--   Heat Data: sqw nonneg
-- statement:
--   The Heat Data construction uses the sqw nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4216-L4216
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4216-L4216

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

theorem Auto.HeatData.sqw_nonneg (p σ : Fin 3 → ℝ) (k : Fin 3) (i : ι) : 0 ≤ Hd.sqw p σ k i := by sorry
