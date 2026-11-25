-- Prove2me | Theorems.Thm_ErdosPosa_ncard_eq_sum_ite
-- name    : ErdosPosa.ncard_eq_sum_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:38.7179+00:00
-- url     : https://prove2.me/theorems/c80a03fc-c1af-4f56-b284-49842cb58436
-- title:
--   Erdos Posa: ncard eq sum ite
-- statement:
--   The Erdos Posa construction uses the ncard eq sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L36-L39
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L36-L39

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.ncard_eq_sum_ite [Fintype V] (p : V → Prop) [DecidablePred p] :
    {x | p x}.ncard = ∑ x, if p x then 1 else 0 := by sorry
