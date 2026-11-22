-- Prove2me | Theorems.Thm_Auto_matCost_ne_top
-- name    : Auto.matCost_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:36.418252+00:00
-- url     : https://prove2.me/theorems/17906cfc-fc8a-4b7f-906e-9d0894e4ba81
-- title:
--   Auto: mat Cost ne top
-- statement:
--   The Auto construction uses the mat Cost ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1059-L1060
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1059-L1060

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

theorem Auto.matCost_ne_top {P : Matrix n n ℂ} (hP : P.PosDef) (K : Matrix n n ℂ) :
    matCost P K ≠ ⊤ := by sorry
