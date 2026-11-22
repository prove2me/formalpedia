-- Prove2me | Theorems.Thm_Auto_three_halves_sub_nonneg
-- name    : Auto.three_halves_sub_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:49:48.288568+00:00
-- url     : https://prove2.me/theorems/e7db353f-8942-4ddb-97e5-eab4cd21913e
-- title:
--   Auto: three halves sub nonneg
-- statement:
--   The Auto construction uses the three halves sub nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4402-L4405
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4402-L4405

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem Auto.three_halves_sub_nonneg {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    0 ≤ (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ) := by sorry
