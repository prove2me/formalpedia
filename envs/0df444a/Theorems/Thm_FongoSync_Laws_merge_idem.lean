-- Prove2me | Theorems.Thm_FongoSync_Laws_merge_idem
-- name    : FongoSync.Laws.merge_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:48.056213+00:00
-- url     : https://prove2.me/theorems/35e462fd-b45e-42c9-8f9a-3a0f3516aa60
-- title:
--   Laws: merge idem
-- statement:
--   Merging a register with itself changes nothing.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L60-L61
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L60-L61

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_merge_idem

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.merge_idem (s : Strategy) (a : Option (Entry V)) : merge s a a = a := by sorry
