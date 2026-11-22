-- Prove2me | Theorems.Thm_Auto_T_eq
-- name    : Auto.T_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:14.09394+00:00
-- url     : https://prove2.me/theorems/ab4f854e-9a63-4ad9-b540-7e974ec1332d
-- title:
--   Auto: T eq
-- statement:
--   The Auto construction uses the T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8675-L8678
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8675-L8678

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

theorem Auto.T_eq (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    Triangular.T F₀ F₁ F₂ = triangularHilbert F₀ F₁ F₂ := by sorry
