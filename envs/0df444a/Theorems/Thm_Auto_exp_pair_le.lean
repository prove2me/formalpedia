-- Prove2me | Theorems.Thm_Auto_exp_pair_le
-- name    : Auto.exp_pair_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:50:29.368585+00:00
-- url     : https://prove2.me/theorems/3b78203a-a22d-487c-81ce-880514887463
-- title:
--   Auto: exp pair le
-- statement:
--   The Auto construction uses the exp pair le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4749-L4765
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4749-L4765

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

theorem Auto.exp_pair_le (a b c : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (-(a ^ 2 + b ^ 2) * x) * Real.exp (-(a + b + c) ^ 2 * y) ≤ Real.exp (-(min x y / 4)
      * (a ^ 2 + b ^ 2 + c ^ 2)) := by sorry
