-- Prove2me | Theorems.Thm_Auto_abs_gaussianD_nodes_le
-- name    : Auto.abs_gaussianD_nodes_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:29.761716+00:00
-- url     : https://prove2.me/theorems/40bdb861-91c6-4ef4-80ce-274bfe40b2d2
-- title:
--   Auto: abs gaussian D nodes le
-- statement:
--   The Auto construction uses the abs gaussian D nodes le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4096-L4111
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4096-L4111

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

theorem Auto.abs_gaussianD_nodes_le {ι : Type*} [Finite ι] (u : ι → ℝ) (j : ℕ) {σa σb : ℝ}
    (ha : 0 < σa) (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σa σb, ∀ q i, |gaussianD j σ (u i - q)| ≤ C * edec σb q ^ 2 := by sorry
