-- Prove2me | Theorems.Thm_Auto_sqrt_smul_eq
-- name    : Auto.sqrt_smul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:36.010261+00:00
-- url     : https://prove2.me/theorems/9946d416-f536-47a2-8c1e-7c256e685522
-- title:
--   Auto: sqrt smul eq
-- statement:
--   The Auto construction uses the sqrt smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1551-L1560
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1551-L1560

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem Auto.sqrt_smul_eq {n : Type*} [Fintype n] {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) :
    open scoped Classical in CFC.sqrt ((a : ℂ) • Q) = ((√a : ℝ) : ℂ) • CFC.sqrt Q := by sorry
