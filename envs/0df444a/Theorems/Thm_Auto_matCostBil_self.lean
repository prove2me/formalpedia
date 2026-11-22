-- Prove2me | Theorems.Thm_Auto_matCostBil_self
-- name    : Auto.matCostBil_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:17.584629+00:00
-- url     : https://prove2.me/theorems/4d674c23-5b2e-4d58-b127-67bbb1791018
-- title:
--   Auto: mat Cost Bil self
-- statement:
--   The Auto construction uses the mat Cost Bil self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1086-L1091
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1086-L1091

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

theorem Auto.matCostBil_self {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCostBil P K K = (matCost P K).toReal := by sorry
