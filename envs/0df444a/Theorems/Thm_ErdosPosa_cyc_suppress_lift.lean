-- Prove2me | Theorems.Thm_ErdosPosa_cyc_suppress_lift
-- name    : ErdosPosa.cyc_suppress_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:23:38.18332+00:00
-- url     : https://prove2.me/theorems/c4c18524-2b45-4cdf-be29-1adbed714595
-- title:
--   Erdos Posa: cyc suppress lift
-- statement:
--   The Erdos Posa construction uses the cyc suppress lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L46-L122
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean#L46-L122

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

theorem ErdosPosa.cyc_suppress_lift {H : SimpleGraph V} {x a b : V} (hxa : H.Adj x a) (hxb : H.Adj x b)
    {S : Set V} (h : Cyc (suppress H x a b) S) : Cyc H (insert x S) := by sorry
