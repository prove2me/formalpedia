-- Prove2me | Theorems.Thm_ErdosPosa_exists_minCyc
-- name    : ErdosPosa.exists_minCyc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:23.599483+00:00
-- url     : https://prove2.me/theorems/6446f51e-8636-53b1-a837-b353bcf037cd
-- title:
--   Erdos Posa: exists min Cyc
-- statement:
--   The Erdos Posa construction uses the exists min Cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L241-L252
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L241-L252

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.exists_minCyc [Finite V] {H : SimpleGraph V} {S : Set V} (h : Cyc H S) :
    ∃ T ⊆ S, MinCyc H T := by sorry
