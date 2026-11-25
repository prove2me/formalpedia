-- Prove2me | Theorems.Thm_ErdosPosa_deg_suppress
-- name    : ErdosPosa.deg_suppress
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:24:05.773716+00:00
-- url     : https://prove2.me/theorems/cd204f8f-0549-4958-b011-985d9ed4da2e
-- title:
--   Erdos Posa: deg suppress
-- statement:
--   The Erdos Posa construction uses the deg suppress property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L125-L202
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L125-L202

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
open Classical

theorem ErdosPosa.deg_suppress [Finite V] {H : SimpleGraph V} {x a b : V} (hN : H.neighborSet x = {a, b})
    (hab : a ≠ b) (hnab : ¬ H.Adj a b) (v : V) :
    deg (suppress H x a b) v = if v = x then 0 else deg H v := by sorry
