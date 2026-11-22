-- Prove2me | Theorems.Thm_Auto_abs_gaussianD_le_unif
-- name    : Auto.abs_gaussianD_le_unif
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:46.801155+00:00
-- url     : https://prove2.me/theorems/66f9e2d3-b0a6-4c13-941d-36103dc1bf1d
-- title:
--   Auto: abs gaussian D le unif
-- statement:
--   The Auto construction uses the abs gaussian D le unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4056-L4071
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4056-L4071

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

theorem Auto.abs_gaussianD_le_unif (j : ℕ) {σa σb : ℝ} (ha : 0 < σa) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σa σb, ∀ t, |gaussianD j σ t| ≤ C * Real.exp (-(t ^ 2) / (4 *
      σb)) := by sorry
