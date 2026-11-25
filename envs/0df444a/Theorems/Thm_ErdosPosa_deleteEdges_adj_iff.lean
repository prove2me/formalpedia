-- Prove2me | Theorems.Thm_ErdosPosa_deleteEdges_adj_iff
-- name    : ErdosPosa.deleteEdges_adj_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:06.947281+00:00
-- url     : https://prove2.me/theorems/0dc3b57d-f0b7-46af-9f07-514411c2518b
-- title:
--   Erdos Posa: delete Edges adj iff
-- statement:
--   The Erdos Posa construction uses the delete Edges adj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L65-L67
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L65-L67

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.deleteEdges_adj_iff {G : SimpleGraph V} {u v a b : V} :
    (G.deleteEdges {s(u, v)}).Adj a b ↔ G.Adj a b ∧ s(a, b) ≠ s(u, v) := by sorry
