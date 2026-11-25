-- Prove2me | Theorems.Thm_ErdosPosa_restr_adj
-- name    : ErdosPosa.restr_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:52.207863+00:00
-- url     : https://prove2.me/theorems/250cce82-b4d9-57ff-8f28-2d150f367643
-- title:
--   Erdos Posa: restr adj
-- statement:
--   The Erdos Posa construction uses the restr adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L38-L39
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L38-L39

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.restr_adj {H : SimpleGraph V} {S : Set V} {a b : V} :
    (restr H S).Adj a b ↔ H.Adj a b ∧ a ∈ S ∧ b ∈ S := by sorry
