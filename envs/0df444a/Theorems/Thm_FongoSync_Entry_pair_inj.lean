-- Prove2me | Theorems.Thm_FongoSync_Entry_pair_inj
-- name    : FongoSync.Entry.pair_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:01.879044+00:00
-- url     : https://prove2.me/theorems/99da22ff-38f5-44a4-8a53-01814c3c81ac
-- title:
--   Entry: pair inj
-- statement:
--   The Entry construction uses the pair inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L326-L327
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L326-L327

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.Entry.pair_inj {a b : Entry V} (h : a.pair = b.pair) : a = b := by sorry
