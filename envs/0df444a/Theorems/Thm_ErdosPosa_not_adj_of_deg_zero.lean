-- Prove2me | Theorems.Thm_ErdosPosa_not_adj_of_deg_zero
-- name    : ErdosPosa.not_adj_of_deg_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:52.218182+00:00
-- url     : https://prove2.me/theorems/731b00ac-6928-4dfd-9036-a2dcae1b06f1
-- title:
--   Erdos Posa: not adj of deg zero
-- statement:
--   The Erdos Posa construction uses the not adj of deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L70-L75
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L70-L75

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.not_adj_of_deg_zero [Finite V] {H : SimpleGraph V} {v w : V} (h : deg H v = 0) :
    ¬ H.Adj v w := by sorry
