-- Prove2me | Theorems.Thm_Auto_shiftMat_mulVec
-- name    : Auto.shiftMat_mulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:53:43.459308+00:00
-- url     : https://prove2.me/theorems/4507c8ca-415f-474b-8887-545dcba88fda
-- title:
--   Auto: shift Mat mul Vec
-- statement:
--   The Auto construction uses the shift Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6659-L6663
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6659-L6663

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section

theorem Auto.shiftMat_mulVec (v : Fin 3) (x : Fin 3 → ℝ) :
    shiftMat v *ᵥ x = Function.update (planePt ![x 0, x 1]) v (planePt ![x 0, x 1] v + x 2) := by sorry
