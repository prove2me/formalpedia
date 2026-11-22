-- Prove2me | Theorems.Thm_ConfFamily_Indep_symm
-- name    : ConfFamily.Indep.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:36:25.630802+00:00
-- url     : https://prove2.me/theorems/e73a1631-d06b-43a4-9091-e93667caf1bc
-- title:
--   Indep: symm
-- statement:
--   Independence is symmetric.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L65-L67
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Basic.lean#L65-L67

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
variable {F}

theorem ConfFamily.Indep.symm {c : Set F.Event} {e₁ e₂ : F.Event} (h : F.Indep c e₁ e₂) :
    F.Indep c e₂ e₁ := by sorry
