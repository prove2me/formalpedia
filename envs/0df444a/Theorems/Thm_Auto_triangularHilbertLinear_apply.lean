-- Prove2me | Theorems.Thm_Auto_triangularHilbertLinear_apply
-- name    : Auto.triangularHilbertLinear_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:22:29.661816+00:00
-- url     : https://prove2.me/theorems/eb36a45e-27bd-4b6d-ba6d-0143a46fa10b
-- title:
--   Auto: triangular Hilbert Linear apply
-- statement:
--   The Auto construction uses the triangular Hilbert Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8555-L8556
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8555-L8556

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

theorem Auto.triangularHilbertLinear_apply (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularHilbertLinear F₀ F₁ F₂ = triangularHilbert F₀ F₁ F₂ := by sorry

attribute [defeq] Auto.triangularHilbertLinear_apply
