-- Prove2me | Theorems.Thm_Auto_hsSq_le_of_entry_le
-- name    : Auto.hsSq_le_of_entry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:35:23.197648+00:00
-- url     : https://prove2.me/theorems/ba4a795d-30d3-4555-849d-4cc01eff551a
-- title:
--   Auto: hs Sq le of entry le
-- statement:
--   The Auto construction uses the hs Sq le of entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4322-L4328
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4322-L4328

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ]

theorem Auto.hsSq_le_of_entry_le (K : Matrix κ κ ℂ) {c : ℝ} (h : ∀ a b, ‖K a b‖ ≤ c) :
    hsSq K ≤ (Fintype.card κ : ℝ) ^ 2 * c ^ 2 := by sorry
