-- Prove2me | Theorems.Thm_FongoSync_Laws_merge_comm
-- name    : FongoSync.Laws.merge_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:32.770708+00:00
-- url     : https://prove2.me/theorems/0edf5b8b-2849-430c-bcd8-6d2eb972c80e
-- title:
--   Laws: merge comm
-- statement:
--   Merging two registers is commutative when equal clocks mean equal entries.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L49-L52
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L49-L52

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_merge_comm

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.merge_comm (s : Strategy) (a b : Option (Entry V))
    (unique : ∀ x ∈ a, ∀ y ∈ b, x.clock = y.clock → x = y) :
    merge s a b = merge s b a := by sorry
