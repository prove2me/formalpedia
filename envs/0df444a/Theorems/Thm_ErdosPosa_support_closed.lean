-- Prove2me | Theorems.Thm_ErdosPosa_support_closed
-- name    : ErdosPosa.support_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:52.12511+00:00
-- url     : https://prove2.me/theorems/29171b96-80b8-48f7-8c62-9086393d8354
-- title:
--   Erdos Posa: support closed
-- statement:
--   The Erdos Posa construction uses the support closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L73-L77
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L73-L77

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

theorem ErdosPosa.support_closed {G' : SimpleGraph V} {S : Set V} (hS : ∀ a b, G'.Adj a b → a ∈ S → b ∈ S)
    {u v : V} (p : G'.Walk u v) (hu : u ∈ S) : v ∈ S := by sorry
