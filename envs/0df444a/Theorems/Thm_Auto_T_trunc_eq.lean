-- Prove2me | Theorems.Thm_Auto_T_trunc_eq
-- name    : Auto.T_trunc_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:15.025427+00:00
-- url     : https://prove2.me/theorems/e944de37-e37e-4e6e-9663-f2f7c7572c64
-- title:
--   Auto: T trunc eq
-- statement:
--   The Auto construction uses the T trunc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8667-L8673
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8667-L8673

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

theorem Auto.T_trunc_eq (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) :
    Triangular.T_trunc F₀ F₁ F₂ ε = triangularHilbertTruncation F₀ F₁ F₂ ε := by sorry
