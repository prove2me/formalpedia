-- Prove2me | Theorems.Thm_FongoSync_Laws_merge_assoc
-- name    : FongoSync.Laws.merge_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:47.132219+00:00
-- url     : https://prove2.me/theorems/3b6661a9-89e4-4cae-98fc-a55ef27042f1
-- title:
--   Laws: merge assoc
-- statement:
--   Merging registers is associative, with no condition.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L55-L57
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L55-L57

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_merge_assoc

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.merge_assoc (s : Strategy) (a b c : Option (Entry V)) :
    merge s (merge s a b) c = merge s a (merge s b c) := by sorry
