-- Prove2me | Theorems.Thm_ErdosPosa_nbr_deleteEdge_left
-- name    : ErdosPosa.nbr_deleteEdge_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:36.125785+00:00
-- url     : https://prove2.me/theorems/ef7e7f76-9d91-56ac-8a96-06310a5a5290
-- title:
--   Erdos Posa: nbr delete Edge left
-- statement:
--   The Erdos Posa construction uses the nbr delete Edge left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L54-L65
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L54-L65

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
variable [Finite V] {H : SimpleGraph V} {y z : V}
omit [Finite V]

theorem ErdosPosa.nbr_deleteEdge_left (hyz : H.Adj y z) :
    (H.deleteEdges {s(y, z)}).neighborSet y = H.neighborSet y \ {z} := by sorry
