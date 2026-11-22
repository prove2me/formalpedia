-- Prove2me | Theorems.Thm_Auto_abs_Gm_le
-- name    : Auto.abs_Gm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:29.335801+00:00
-- url     : https://prove2.me/theorems/577a28d0-4738-4b0c-81d0-a4474aa95ffa
-- title:
--   Auto: abs Gm le
-- statement:
--   The Auto construction uses the abs Gm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4818-L4824
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4818-L4824

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
open Auto
noncomputable section

theorem Auto.abs_Gm_le (m : ℕ) {β sa sb : ℝ} (hβ : 0 < β) (hsa : 0 < sa) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc sa sb, ∀ p, |Gm β m s p| ≤ C * Real.exp (-(p 0 + p 1 + p 2) ^
      2 / (4 * (β * sb))) := by sorry
