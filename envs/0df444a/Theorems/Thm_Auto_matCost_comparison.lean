-- Prove2me | Theorems.Thm_Auto_matCost_comparison
-- name    : Auto.matCost_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:30:55.060431+00:00
-- url     : https://prove2.me/theorems/95b461dd-4420-4309-b439-b32738fb9685
-- title:
--   Auto: mat Cost comparison
-- statement:
--   The Auto construction uses the mat Cost comparison property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1572-L1598
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1572-L1598

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

theorem Auto.matCost_comparison {P Q : Matrix n n ℂ} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hPQ : P ≤ (a : ℂ) • Q) (K : Matrix n n ℂ) :
    ENNReal.ofReal (√a)⁻¹ * matCost Q K ≤ matCost P K := by sorry
