-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_span_zero_at
-- name    : DeletionCode.WitnessAlgebra.span_zero_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:29.297854+00:00
-- url     : https://prove2.me/theorems/3ec14cda-8cbb-403a-8f2e-96226dc37362
-- title:
--   Witness Algebra: span zero at
-- statement:
--   The Witness Algebra construction uses the span zero at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L58-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L58-L65

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.span_zero_at {H : Type*} (S : Set (H → ℚ)) (h : H)
    (hzero : ∀ w ∈ S, w h = 0) (u : H → ℚ) (hu : u ∈ Submodule.span ℚ S) :
    u h = 0 := by sorry
