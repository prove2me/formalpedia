-- Prove2me | Theorems.Thm_ConfFamily_union_pair_comm
-- name    : ConfFamily.union_pair_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:36:29.199998+00:00
-- url     : https://prove2.me/theorems/5500411a-1aff-4e6f-9559-2291dd744204
-- title:
--   Conf Family: union pair comm
-- statement:
--   Singleton extensions commute.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L52-L54
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L52-L54

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
variable {F}
variable (F)

theorem ConfFamily.union_pair_comm {α : Type*} (s : Set α) (a b : α) :
    s ∪ {a} ∪ {b} = s ∪ {b} ∪ {a} := by sorry
