-- Prove2me | Theorems.Thm_Auto_gaussian_le_sup
-- name    : Auto.gaussian_le_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:44.148202+00:00
-- url     : https://prove2.me/theorems/7ee9ecf6-2f11-4280-b2fb-57bcccb1d812
-- title:
--   Auto: gaussian le sup
-- statement:
--   The Auto construction uses the gaussian le sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5386-L5395
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5386-L5395

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

theorem Auto.gaussian_le_sup (σ t : ℝ) : gaussian σ t ≤ (√(2 * π * σ))⁻¹ := by sorry
