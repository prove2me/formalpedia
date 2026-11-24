-- Prove2me | Theorems.Thm_FongoSync_label_eq_of_connected
-- name    : FongoSync.label_eq_of_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:19.544816+00:00
-- url     : https://prove2.me/theorems/3730c6cb-64c5-4d70-9385-41a584c83dc0
-- title:
--   Fongo Sync: label eq of connected
-- statement:
--   The Fongo Sync construction uses the label eq of connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L66-L67
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L66-L67

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync
variable {P : List Edge} {L : Gid → Gid} (inv : ∀ g, IsCanonical P g (L g))
include inv

theorem FongoSync.label_eq_of_connected {g h : Gid} (c : Connected P g h) : L g = L h := by sorry
