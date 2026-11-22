-- Prove2me | Theorems.Thm_Auto_abs_kernIntegrand_le
-- name    : Auto.abs_kernIntegrand_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:08.28489+00:00
-- url     : https://prove2.me/theorems/48a211c6-c9fa-4b83-b8e0-2b974e4895a5
-- title:
--   Auto: abs kern Integrand le
-- statement:
--   The Auto construction uses the abs kern Integrand le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7723-L7739
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7723-L7739

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

theorem Auto.abs_kernIntegrand_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → ∀ t, |kernIntegrand m s t| ≤ C / (s * √s) := by sorry
