-- Prove2me | Theorems.Thm_Auto_tendsto_T_trunc
-- name    : Auto.tendsto_T_trunc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:44:35.752111+00:00
-- url     : https://prove2.me/theorems/0185265d-1d6d-4a92-9544-56f986699003
-- title:
--   Auto: tendsto T trunc
-- statement:
--   The Auto construction uses the tendsto T trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8680-L8683
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8680-L8683

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

theorem Auto.tendsto_T_trunc (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (Triangular.T_trunc F₀ F₁ F₂) (𝓝[>] 0) (𝓝 (Triangular.T F₀ F₁ F₂)) := by sorry
