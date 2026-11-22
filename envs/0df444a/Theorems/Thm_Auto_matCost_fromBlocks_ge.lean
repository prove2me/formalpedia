-- Prove2me | Theorems.Thm_Auto_matCost_fromBlocks_ge
-- name    : Auto.matCost_fromBlocks_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:25.667583+00:00
-- url     : https://prove2.me/theorems/364b6e22-785d-44a9-9803-5ef974204293
-- title:
--   Auto: mat Cost from Blocks ge
-- statement:
--   The Auto construction uses the mat Cost from Blocks ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3496-L3521
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3496-L3521

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

theorem Auto.matCost_fromBlocks_ge {P1 P2 : Matrix ι ι ℂ} (hP1 : P1.PosSemidef) (hP2 : P2.PosSemidef)
    (K11 K12 K21 K22 : Matrix ι ι ℂ) :
    matCost P1 K11 + matCost P2 K22 ≤ matCost (Matrix.fromBlocks P1 0 0 P2) (Matrix.fromBlocks
      K11 K12 K21 K22) := by sorry
