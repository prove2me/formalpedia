-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_independent_insert
-- name    : DeletionCode.WalkSelection.independent_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:28.788003+00:00
-- url     : https://prove2.me/theorems/639fa893-23f7-4760-9a34-b0afef89f2ab
-- title:
--   Walk Selection: independent insert
-- statement:
--   The Walk Selection construction uses the independent insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L52-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L52-L56

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.independent_insert {step : Fin m → V} {S : Finset (Fin m)}
    (hs : LinearIndepOn ℚ step (S : Set (Fin m))) (i : Fin m)
    (hi : step i ∉ selectedSpan step S) :
    LinearIndepOn ℚ step ((insert i S : Finset (Fin m)) : Set (Fin m)) := by sorry
