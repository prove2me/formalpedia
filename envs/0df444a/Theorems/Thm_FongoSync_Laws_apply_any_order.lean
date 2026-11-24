-- Prove2me | Theorems.Thm_FongoSync_Laws_apply_any_order
-- name    : FongoSync.Laws.apply_any_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:14.405102+00:00
-- url     : https://prove2.me/theorems/95dd6a94-9523-4682-b3b9-c1d6e336d93f
-- title:
--   Laws: apply any order
-- statement:
--   Two changes may arrive in either order, unless they share a clock and differ.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L75-L78
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L75-L78

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_apply_any_order

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.apply_any_order (s : Strategy) (h : Option (Entry V)) (a b : Entry V)
    (unique : a.clock = b.clock → a = b) :
    apply s (apply s h a) b = apply s (apply s h b) a := by sorry
