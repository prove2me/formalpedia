-- Prove2me | Theorems.Thm_FongoSync_length_filter_lt
-- name    : FongoSync.length_filter_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:35.460136+00:00
-- url     : https://prove2.me/theorems/ef99480b-1bb3-485e-a049-30729ccd5c59
-- title:
--   Fongo Sync: length filter lt
-- statement:
--   The Fongo Sync construction uses the length filter lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L91-L105
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L91-L105

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.length_filter_lt {l : List Gid} {p q : Gid → Bool} (hpq : ∀ x ∈ l, p x → q x)
    (hx : ∃ x ∈ l, q x ∧ ¬ p x) : (l.filter p).length < (l.filter q).length := by sorry
