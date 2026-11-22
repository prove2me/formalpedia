-- Prove2me | Theorems.Thm_Auto_costInt_fromBlocks_diag
-- name    : Auto.costInt_fromBlocks_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:28.734019+00:00
-- url     : https://prove2.me/theorems/4754a3d7-d33c-485c-9382-b023c754e8da
-- title:
--   Auto: cost Int from Blocks diag
-- statement:
--   The Auto construction uses the cost Int from Blocks diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3486-L3494
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3486-L3494

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
omit [DecidableEq ι]

theorem Auto.costInt_fromBlocks_diag (A1 A2 K11 K12 K21 K22 X1 X2 : Matrix ι ι ℂ) :
    costInt (Matrix.fromBlocks A1 0 0 A2) (Matrix.fromBlocks K11 K12 K21 K22) (Matrix.fromBlocks
      X1 0 0 X2) = costInt A1 K11 X1 + costInt A2 K22 X2 := by sorry
