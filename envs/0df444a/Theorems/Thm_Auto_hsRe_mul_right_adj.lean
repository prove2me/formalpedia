-- Prove2me | Theorems.Thm_Auto_hsRe_mul_right_adj
-- name    : Auto.hsRe_mul_right_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:02.534076+00:00
-- url     : https://prove2.me/theorems/d3180b08-35ae-4cfe-aa58-7b2aeab68648
-- title:
--   Auto: hs Re mul right adj
-- statement:
--   The Auto construction uses the hs Re mul right adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3871-L3874
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3871-L3874

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
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem Auto.hsRe_mul_right_adj {A : Matrix n n ℂ} (hA : A.IsHermitian) (X Y : Matrix n n ℂ) :
    hsRe X (Y * A) = hsRe (X * A) Y := by sorry
