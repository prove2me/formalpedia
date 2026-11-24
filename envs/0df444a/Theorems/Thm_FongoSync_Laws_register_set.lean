-- Prove2me | Theorems.Thm_FongoSync_Laws_register_set
-- name    : FongoSync.Laws.register_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:21.071802+00:00
-- url     : https://prove2.me/theorems/222fdb2b-6431-4390-95e7-08295fc82031
-- title:
--   Laws: register set
-- statement:
--   A register fed the same set of entries ends the same, whatever the order and repeats.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L86-L89
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L86-L89

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.register_set (s : Strategy) (l₁ l₂ : List (Entry V)) (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (unique : UniqueClocks l₁) :
    l₁.foldl (apply s) none = l₂.foldl (apply s) none := by sorry
