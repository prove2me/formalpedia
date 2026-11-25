-- Prove2me | Theorems.Thm_ErdosPosa_support_restr
-- name    : ErdosPosa.support_restr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:04.50301+00:00
-- url     : https://prove2.me/theorems/ce2af889-e68f-5c0d-b19c-8afc3b6297fb
-- title:
--   Erdos Posa: support restr
-- statement:
--   The Erdos Posa construction uses the support restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L63-L65
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L63-L65

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.support_restr {G : SimpleGraph V} {X : Set V} {a b : V} (p : (restr G X).Walk a b)
    (ha : a ∈ X) : ∀ y ∈ p.support, y ∈ X := by sorry
