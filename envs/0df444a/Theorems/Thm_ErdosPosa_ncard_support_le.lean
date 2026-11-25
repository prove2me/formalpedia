-- Prove2me | Theorems.Thm_ErdosPosa_ncard_support_le
-- name    : ErdosPosa.ncard_support_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:21:43.676147+00:00
-- url     : https://prove2.me/theorems/bc526130-336e-4fb0-82f8-abb50b9eaf83
-- title:
--   Erdos Posa: ncard support le
-- statement:
--   The Erdos Posa construction uses the ncard support le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L46-L50
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L46-L50

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}

theorem ErdosPosa.ncard_support_le {u v : V} (p : H.Walk u v) : {y | y ∈ p.support}.ncard ≤ p.length + 1 := by sorry
