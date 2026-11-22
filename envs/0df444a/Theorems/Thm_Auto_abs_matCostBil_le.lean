-- Prove2me | Theorems.Thm_Auto_abs_matCostBil_le
-- name    : Auto.abs_matCostBil_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:24.985803+00:00
-- url     : https://prove2.me/theorems/2411f753-9bb4-4b87-9da4-8c8c14364dbe
-- title:
--   Auto: abs mat Cost Bil le
-- statement:
--   The Auto construction uses the abs mat Cost Bil le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1094-L1125
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1094-L1125

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m]

theorem Auto.abs_matCostBil_le {P : Matrix n n ℂ} (hP : P.PosDef) (K L : Matrix n n ℂ) :
    |matCostBil P K L| ≤ √(matCost P K).toReal * √(matCost P L).toReal := by sorry
