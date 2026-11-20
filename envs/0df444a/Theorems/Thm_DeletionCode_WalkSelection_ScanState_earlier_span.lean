-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_ScanState_earlier_span
-- name    : DeletionCode.WalkSelection.ScanState.earlier_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:19.286185+00:00
-- url     : https://prove2.me/theorems/6468546c-9007-413f-9ca4-a3d84369a9e6
-- title:
--   Scan State: earlier span
-- statement:
--   The Scan State construction uses the earlier span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L46-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L46-L50

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.ScanState.earlier_span {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (h : ScanState step Good n S)
    (j : Fin m) (hj : j.val < n) : step j ∈ selectedSpan step S := by sorry
