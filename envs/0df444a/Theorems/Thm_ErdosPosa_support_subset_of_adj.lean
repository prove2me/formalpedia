-- Prove2me | Theorems.Thm_ErdosPosa_support_subset_of_adj
-- name    : ErdosPosa.support_subset_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:01.51341+00:00
-- url     : https://prove2.me/theorems/a7807a44-efd3-508d-8a74-4069f4c0788b
-- title:
--   Erdos Posa: support subset of adj
-- statement:
--   The Erdos Posa construction uses the support subset of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L280-L289
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L280-L289

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.support_subset_of_adj {G : SimpleGraph V} {T : Set V} (hG : ∀ a b, G.Adj a b → b ∈ T)
    {u v : V} (p : G.Walk u v) (hu : u ∈ T) : ∀ x ∈ p.support, x ∈ T := by sorry
