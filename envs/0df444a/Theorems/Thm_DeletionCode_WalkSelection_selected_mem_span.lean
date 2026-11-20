-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_selected_mem_span
-- name    : DeletionCode.WalkSelection.selected_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:13:56.872939+00:00
-- url     : https://prove2.me/theorems/c010920e-cfc9-4978-946b-4132751b217d
-- title:
--   Walk Selection: selected mem span
-- statement:
--   The Walk Selection construction uses the selected mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L25-L27
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L25-L27

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.selected_mem_span (step : Fin m → V) (S : Finset (Fin m))
    (r : Fin m) (hr : r ∈ S) : step r ∈ selectedSpan step S := by sorry
