-- Prove2me | Theorems.Thm_ErdosPosa_MinCyc_two_nbrs
-- name    : ErdosPosa.MinCyc.two_nbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:44.050699+00:00
-- url     : https://prove2.me/theorems/8ca7db67-0377-4691-a45d-906bc43e8bdb
-- title:
--   Min Cyc: two nbrs
-- statement:
--   The Min Cyc construction uses the two nbrs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L254-L261
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L254-L261

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.MinCyc.two_nbrs {H : SimpleGraph V} {T : Set V} (h : MinCyc H T) {x : V} (hx : x ∈ T) :
    ∃ y z, y ∈ T ∧ z ∈ T ∧ y ≠ z ∧ H.Adj x y ∧ H.Adj x z := by sorry
