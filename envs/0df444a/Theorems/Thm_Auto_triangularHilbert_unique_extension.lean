-- Prove2me | Theorems.Thm_Auto_triangularHilbert_unique_extension
-- name    : Auto.triangularHilbert_unique_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T19:44:25.128377+00:00
-- url     : https://prove2.me/theorems/0d95dae4-b6c0-4eb6-82d1-5ef0920f50eb
-- title:
--   Auto: triangular Hilbert unique extension
-- statement:
--   Source Theorem 1: unique bounded complex trilinear extension to L3(R2), with the same bound.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8633-L8648
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8633-L8648

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

theorem Auto.triangularHilbert_unique_extension :
    ∃ T : TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] ℂ,
      (∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
        T (F₀.toLp 3) (F₁.toLp 3) (F₂.toLp 3) = triangularHilbert F₀ F₁ F₂) ∧
      (∀ f₀ f₁ f₂, ‖T f₀ f₁ f₂‖ ≤ triangularBoundConstant * ‖f₀‖ * ‖f₁‖ * ‖f₂‖) ∧
      ∀ S : TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] ℂ,
        (∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
          S (F₀.toLp 3) (F₁.toLp 3) (F₂.toLp 3) = triangularHilbert F₀ F₁ F₂) → S = T := by sorry
