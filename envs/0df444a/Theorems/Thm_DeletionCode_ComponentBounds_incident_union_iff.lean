-- Prove2me | Theorems.Thm_DeletionCode_ComponentBounds_incident_union_iff
-- name    : DeletionCode.ComponentBounds.incident_union_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:12:20.385916+00:00
-- url     : https://prove2.me/theorems/f88cff18-f815-490c-b4b0-5e9b9324d6b2
-- title:
--   Component Bounds: incident union iff
-- statement:
--   The Component Bounds construction uses the incident union iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentBounds.lean#L48-L61
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentBounds.lean#L48-L61

import Definitions.Def_DeletionCode_RuleSetGraph
import Mathlib.Data.Fintype.Sum
import Definitions.Def_DeletionCode_ComponentBounds
set_option autoImplicit true
open DeletionCode DeletionCode.ComponentBounds
open SignedSupport SupportComponents RuleSetGraph

theorem DeletionCode.ComponentBounds.incident_union_iff {L : ℕ} (Q S : Finset (Gram L → ℤ)) (v : Vertex L) :
    Incident (Q ∪ S) v ↔ Incident Q v ∨ Incident S v := by sorry
