-- Prove2me | Theorems.Thm_Auto_re_trace_le_of_entry_le
-- name    : Auto.re_trace_le_of_entry_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:35:29.370701+00:00
-- url     : https://prove2.me/theorems/64b1c834-c225-4595-8a0f-9202c8bd14be
-- title:
--   Auto: re trace le of entry le
-- statement:
--   The Auto construction uses the re trace le of entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4338-L4343
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4338-L4343

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

theorem Auto.re_trace_le_of_entry_le (Γ : Matrix κ κ ℂ) {c : ℝ} (h : ∀ a b, ‖Γ a b‖ ≤ c) :
    Γ.trace.re ≤ Fintype.card κ * c := by sorry
