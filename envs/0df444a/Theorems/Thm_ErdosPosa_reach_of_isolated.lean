-- Prove2me | Theorems.Thm_ErdosPosa_reach_of_isolated
-- name    : ErdosPosa.reach_of_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:15.640498+00:00
-- url     : https://prove2.me/theorems/4c78aa60-8b3e-484b-9849-3e9a6e731d5a
-- title:
--   Erdos Posa: reach of isolated
-- statement:
--   The Erdos Posa construction uses the reach of isolated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L49-L54
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L49-L54

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.reach_of_isolated {G : SimpleGraph V} {x y : V} (hx : ∀ z, ¬ G.Adj x z)
    (h : G.Reachable x y) : x = y := by sorry
