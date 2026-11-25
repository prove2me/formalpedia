-- Prove2me | Theorems.Thm_ErdosPosa_not_isAcyclic_induce_iff
-- name    : ErdosPosa.not_isAcyclic_induce_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:13.91919+00:00
-- url     : https://prove2.me/theorems/47fd6bf9-4596-57d8-a9aa-445aad16539d
-- title:
--   Erdos Posa: not is Acyclic induce iff
-- statement:
--   The Erdos Posa construction uses the not is Acyclic induce iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L77-L109
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L77-L109

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.not_isAcyclic_induce_iff {G : SimpleGraph V} {S : Set V} :
    ¬ (G.induce S).IsAcyclic ↔ Cyc G S := by sorry
