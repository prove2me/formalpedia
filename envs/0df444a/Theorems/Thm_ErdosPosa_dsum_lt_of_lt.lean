-- Prove2me | Theorems.Thm_ErdosPosa_dsum_lt_of_lt
-- name    : ErdosPosa.dsum_lt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:50.650477+00:00
-- url     : https://prove2.me/theorems/fd6ad8bc-b91c-5d2c-999f-1bdf0359b656
-- title:
--   Erdos Posa: dsum lt of lt
-- statement:
--   The Erdos Posa construction uses the dsum lt of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L37-L47
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L37-L47

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

theorem ErdosPosa.dsum_lt_of_lt [Fintype V] {H K : SimpleGraph V} (hHK : H ≤ K) {u v : V} (huv : K.Adj u v)
    (hn : ¬ H.Adj u v) : dsum H < dsum K := by sorry
