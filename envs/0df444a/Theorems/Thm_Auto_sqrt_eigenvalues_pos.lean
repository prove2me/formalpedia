-- Prove2me | Theorems.Thm_Auto_sqrt_eigenvalues_pos
-- name    : Auto.sqrt_eigenvalues_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:10.440455+00:00
-- url     : https://prove2.me/theorems/883b8d39-ce64-44e8-ac0f-45dedc040b60
-- title:
--   Auto: sqrt eigenvalues pos
-- statement:
--   The Auto construction uses the sqrt eigenvalues pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1030-L1031
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1030-L1031

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

theorem Auto.sqrt_eigenvalues_pos {P : Matrix n n ℂ} (hP : P.PosDef) (i : n) : 0 < √(hP.1.eigenvalues i) := by sorry
