-- Prove2me | Theorems.Thm_ErdosPosa_cyc_mono
-- name    : ErdosPosa.cyc_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:06.19007+00:00
-- url     : https://prove2.me/theorems/b5c61305-388e-5d04-ba84-ce0f333c9a3e
-- title:
--   Erdos Posa: cyc mono
-- statement:
--   The Erdos Posa construction uses the cyc mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L69-L75
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L69-L75

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.cyc_mono {H H' : SimpleGraph V} {S S' : Set V} (h : Cyc H S) (hH : H ≤ H')
    (hS : S ⊆ S') : Cyc H' S' := by sorry
