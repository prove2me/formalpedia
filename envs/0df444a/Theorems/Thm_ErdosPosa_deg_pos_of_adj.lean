-- Prove2me | Theorems.Thm_ErdosPosa_deg_pos_of_adj
-- name    : ErdosPosa.deg_pos_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:50.839275+00:00
-- url     : https://prove2.me/theorems/26ffa48a-e513-4b37-b9d3-44c4197ed8f2
-- title:
--   Erdos Posa: deg pos of adj
-- statement:
--   The Erdos Posa construction uses the deg pos of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L204-L205
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L204-L205

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Definitions.Def_ErdosPosaLib_EPShort
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.deg_pos_of_adj [Finite V] {H : SimpleGraph V} {u w : V} (h : H.Adj u w) : 0 < deg H u := by sorry
