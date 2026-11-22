-- Prove2me | Theorems.Thm_Auto_trace_cyclic_diag
-- name    : Auto.trace_cyclic_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:57.967143+00:00
-- url     : https://prove2.me/theorems/df655148-119d-430b-96a9-c5d2772c6ebc
-- title:
--   Auto: trace cyclic diag
-- statement:
--   The Auto construction uses the trace cyclic diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6269-L6282
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6269-L6282

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Auto.trace_cyclic_diag (x₀ x₁ x₂ r₀ r₁ r₂ : ι → ℝ) (B₀ B₁ B₂ : Matrix ι ι ℂ) :
    (rdiag x₀ * (rdiag r₀ * B₀ * rdiag r₁) * rdiag x₁ * (rdiag r₁ * B₁ * rdiag r₂) * rdiag x₂ *
      (rdiag r₂ * B₂ * rdiag r₀)).trace = ∑ i, ∑ j, ∑ k, B₀ i j * B₁ j k * B₂ k i * ((x₀ i * r₀ i
      ^ 2 : ℝ) * (x₁ j * r₁ j ^ 2 : ℝ) * (x₂ k * r₂ k ^ 2 : ℝ) : ℝ) := by sorry
