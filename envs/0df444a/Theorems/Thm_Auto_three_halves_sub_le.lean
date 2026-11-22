-- Prove2me | Theorems.Thm_Auto_three_halves_sub_le
-- name    : Auto.three_halves_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:49:43.371635+00:00
-- url     : https://prove2.me/theorems/20d2dd01-c736-4ead-9ff6-89560ffcc122
-- title:
--   Auto: three halves sub le
-- statement:
--   The Auto construction uses the three halves sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4388-L4400
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4388-L4400

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

theorem Auto.three_halves_sub_le {x η : ℝ} (hx : 0 ≤ x) (hη : 0 ≤ η) :
    (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ) ≤ 2 * x * √(x + η) := by sorry
