-- Prove2me | Theorems.Thm_Auto_hsRe_mul_left_adj
-- name    : Auto.hsRe_mul_left_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:52.053528+00:00
-- url     : https://prove2.me/theorems/5b545848-5c06-4e63-acad-188079c38a9c
-- title:
--   Auto: hs Re mul left adj
-- statement:
--   The Auto construction uses the hs Re mul left adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3866-L3868
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3866-L3868

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

theorem Auto.hsRe_mul_left_adj {A : Matrix n n ℂ} (hA : A.IsHermitian) (X Y : Matrix n n ℂ) :
    hsRe X (A * Y) = hsRe (A * X) Y := by sorry
