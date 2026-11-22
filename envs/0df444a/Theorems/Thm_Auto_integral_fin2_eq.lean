-- Prove2me | Theorems.Thm_Auto_integral_fin2_eq
-- name    : Auto.integral_fin2_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:09.998541+00:00
-- url     : https://prove2.me/theorems/9e903c93-65ba-4d1f-af70-9c8544d3bb36
-- title:
--   Auto: integral fin2 eq
-- statement:
--   The Auto construction uses the integral fin2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7547-L7549
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7547-L7549

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

theorem Auto.integral_fin2_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ × ℝ → E) :
    ∫ x : Fin 2 → ℝ, f (x 0, x 1) = ∫ p, f p := by sorry
