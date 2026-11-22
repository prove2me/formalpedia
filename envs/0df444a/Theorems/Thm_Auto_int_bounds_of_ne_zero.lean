-- Prove2me | Theorems.Thm_Auto_int_bounds_of_ne_zero
-- name    : Auto.int_bounds_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:05.155953+00:00
-- url     : https://prove2.me/theorems/800c5bcc-ec52-489e-83d1-aa17450a627d
-- title:
--   Auto: int bounds of ne zero
-- statement:
--   The Auto construction uses the int bounds of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7438-L7446
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7438-L7446

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.int_bounds_of_ne_zero {F : ℝ × ℝ → ℂ} {ρ : ℝ}
    (hF : ∀ p, ρ < ‖p‖ → F p = 0) {N : ℕ} (hN : 0 < N)
    {a b : ℤ} (hp : F ((a : ℝ) / N, (b : ℝ) / N) ≠ 0) :
    (|a| : ℝ) ≤ ρ * N ∧ (|b| : ℝ) ≤ ρ * N := by sorry
