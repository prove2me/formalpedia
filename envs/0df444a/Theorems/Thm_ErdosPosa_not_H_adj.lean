-- Prove2me | Theorems.Thm_ErdosPosa_not_H_adj
-- name    : ErdosPosa.not_H_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:44.134495+00:00
-- url     : https://prove2.me/theorems/2e4ecfaf-43f9-46f1-905f-ad3c519f5deb
-- title:
--   Erdos Posa: not H adj
-- statement:
--   The Erdos Posa construction uses the not H adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L81-L87
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L81-L87

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
variable [Finite V] {G H : SimpleGraph V}

theorem ErdosPosa.not_H_adj {c d a : V} (hcd : c ≠ d) (hc : c = a ∨ deg H c = 0) (hd : d = a ∨ deg H d = 0) :
    ¬ H.Adj c d := by sorry
