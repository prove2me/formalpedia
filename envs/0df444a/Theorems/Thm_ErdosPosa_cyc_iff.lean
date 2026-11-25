-- Prove2me | Theorems.Thm_ErdosPosa_cyc_iff
-- name    : ErdosPosa.cyc_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:53.521592+00:00
-- url     : https://prove2.me/theorems/fca064fe-2aad-594f-a8bb-a519eadf7d8f
-- title:
--   Erdos Posa: cyc iff
-- statement:
--   The Erdos Posa construction uses the cyc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L56-L63
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L56-L63

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.cyc_iff {H : SimpleGraph V} {S : Set V} :
    Cyc H S ↔ ∃ u v, (restr H S).Adj u v ∧ ((restr H S).deleteEdges {s(u, v)}).Reachable u v := by sorry
