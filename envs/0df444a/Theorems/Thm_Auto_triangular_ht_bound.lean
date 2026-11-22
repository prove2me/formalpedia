-- Prove2me | Theorems.Thm_Auto_triangular_ht_bound
-- name    : Auto.triangular_ht_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:38:28.784723+00:00
-- url     : https://prove2.me/theorems/d6cd8c34-ec6f-4a2f-a1af-516bbd63d445
-- title:
--   Auto: triangular ht bound
-- statement:
--   The Auto construction uses the triangular ht bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8685-L8697
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8685-L8697

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

theorem Auto.triangular_ht_bound :
    ∃ C : ℝ, ∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
      ‖Triangular.T F₀ F₁ F₂‖ₑ ≤
        ENNReal.ofReal C * eLpNorm F₀ 3 * eLpNorm F₁ 3 * eLpNorm F₂ 3 := by sorry
