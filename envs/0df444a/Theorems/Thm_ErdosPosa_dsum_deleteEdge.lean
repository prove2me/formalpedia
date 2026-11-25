-- Prove2me | Theorems.Thm_ErdosPosa_dsum_deleteEdge
-- name    : ErdosPosa.dsum_deleteEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:25.121216+00:00
-- url     : https://prove2.me/theorems/1fa43228-92a5-4252-886b-3274a5c2d836
-- title:
--   Erdos Posa: dsum delete Edge
-- statement:
--   The Erdos Posa construction uses the dsum delete Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L148-L155
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L148-L155

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
variable [Fintype V]

theorem ErdosPosa.dsum_deleteEdge (hyz : H.Adj y z) : dsum (H.deleteEdges {s(y, z)}) < dsum H := by sorry
