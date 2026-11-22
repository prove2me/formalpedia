-- Prove2me | Theorems.Thm_Auto_exp_shift_le
-- name    : Auto.exp_shift_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:26.54725+00:00
-- url     : https://prove2.me/theorems/f0a42f8c-e223-4460-a93f-26608f7e76c3
-- title:
--   Auto: exp shift le
-- statement:
--   The Auto construction uses the exp shift le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4073-L4081
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4073-L4081

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

theorem Auto.exp_shift_le (u q : ℝ) {c : ℝ} (hc : 0 < c) :
    Real.exp (-((u - q) ^ 2) / (4 * c)) ≤ Real.exp (u ^ 2 / (4 * c)) * Real.exp (-(q ^ 2) / (8 *
      c)) := by sorry
