-- Prove2me | Theorems.Thm_Auto_sum_three_eq
-- name    : Auto.sum_three_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:26.783474+00:00
-- url     : https://prove2.me/theorems/a872b373-9fdb-4f78-82d5-6ede45e43b9b
-- title:
--   Auto: sum three eq
-- statement:
--   The Auto construction uses the sum three eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4767-L4781
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4767-L4781

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

theorem Auto.sum_three_eq (v : Fin 3) (p : Fin 3 → ℝ) :
    p 0 + p 1 + p 2 = p v + p (v + 1) + p (v - 1) ∧ p 0 + p 1 + p 2 = p v + p (v - 1) + p (v +
      1) ∧ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = p v ^ 2 + p (v + 1) ^ 2 + p (v - 1) ^ 2 ∧ p 0 ^ 2 + p 1 ^
      2 + p 2 ^ 2 = p v ^ 2 + p (v - 1) ^ 2 + p (v + 1) ^ 2 := by sorry
