-- Prove2me | Theorems.Thm_Auto_triangularHilbert_bound
-- name    : Auto.triangularHilbert_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:29:21.962211+00:00
-- url     : https://prove2.me/theorems/8f8a597b-0670-4294-bec0-aeb18c59d7cb
-- title:
--   Auto: triangular Hilbert bound
-- statement:
--   The Auto construction uses the triangular Hilbert bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8446-L8480
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8446-L8480

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

theorem Auto.triangularHilbert_bound (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    ‖triangularHilbert F₀ F₁ F₂‖ ≤ triangularBoundConstant *
      (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal := by sorry
