-- Prove2me | Theorems.Thm_FongoSync_ownerAllowsB_iff
-- name    : FongoSync.ownerAllowsB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:54.99025+00:00
-- url     : https://prove2.me/theorems/ba2887b9-1ca1-489d-857d-161c62d10cca
-- title:
--   Fongo Sync: owner Allows B iff
-- statement:
--   The Fongo Sync construction uses the owner Allows B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L183-L189
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L183-L189

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.ownerAllowsB_iff {live : Gid → Bool} {p : Gid → Prop} (h : ∀ m, live m = true ↔ p m)
    (v : Option (Entry Value)) : ownerAllowsB inp live v = true ↔ ownerAllows inp p v := by sorry
