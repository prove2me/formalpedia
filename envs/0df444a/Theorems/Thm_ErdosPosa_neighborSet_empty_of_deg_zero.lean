-- Prove2me | Theorems.Thm_ErdosPosa_neighborSet_empty_of_deg_zero
-- name    : ErdosPosa.neighborSet_empty_of_deg_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:39.170615+00:00
-- url     : https://prove2.me/theorems/e979bbc7-2067-52be-ad7f-cd361a9e1985
-- title:
--   Erdos Posa: neighbor Set empty of deg zero
-- statement:
--   The Erdos Posa construction uses the neighbor Set empty of deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L66-L68
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L66-L68

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

theorem ErdosPosa.neighborSet_empty_of_deg_zero [Finite V] {H : SimpleGraph V} {v : V} (h : deg H v = 0) :
    H.neighborSet v = ∅ := by sorry
