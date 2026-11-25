-- Prove2me | Theorems.Thm_ErdosPosa_dist_le_of_mem_support
-- name    : ErdosPosa.dist_le_of_mem_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:21:47.993109+00:00
-- url     : https://prove2.me/theorems/24d74a67-64f9-4057-9cdd-ee2cc1dcef31
-- title:
--   Erdos Posa: dist le of mem support
-- statement:
--   The Erdos Posa construction uses the dist le of mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L33-L38
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L33-L38

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

theorem ErdosPosa.dist_le_of_mem_support {v x y : V} (q : H.Walk v x) (hq : q.length = H.dist v x)
    (hy : y ∈ q.support) : H.dist v y ≤ H.dist v x := by sorry
