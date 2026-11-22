-- Prove2me | Theorems.Thm_Auto_triangularHilbertTruncation_eq
-- name    : Auto.triangularHilbertTruncation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:58:10.007808+00:00
-- url     : https://prove2.me/theorems/21118985-c304-4b34-813e-448c1ebb360d
-- title:
--   Auto: triangular Hilbert Truncation eq
-- statement:
--   The Auto construction uses the triangular Hilbert Truncation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8353-L8360
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8353-L8360

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

theorem Auto.triangularHilbertTruncation_eq (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) :
    triangularHilbertTruncation F₀ F₁ F₂ ε = -triangularTruncation F₀ (triangularPullback₁ F₁)
      (triangularPullback₂ F₂) ε := by sorry
