-- Prove2me | Theorems.Thm_Auto_exists_support_bound
-- name    : Auto.exists_support_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:19.496632+00:00
-- url     : https://prove2.me/theorems/05987c90-8c88-4894-b2aa-cb3ae349b621
-- title:
--   Auto: exists support bound
-- statement:
--   The Auto construction uses the exists support bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7539-L7545
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7539-L7545

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

theorem Auto.exists_support_bound {f : ℝ × ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ ρ, 0 ≤ ρ ∧ ∀ p, ρ < ‖p‖ → f p = 0 := by sorry
