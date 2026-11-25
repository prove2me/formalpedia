-- Prove2me | Theorems.Thm_ErdosPosa_psi_deleteEdge_of_deg_one
-- name    : ErdosPosa.psi_deleteEdge_of_deg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:56.704392+00:00
-- url     : https://prove2.me/theorems/23d6ce11-0bbd-45fd-92df-cbf9b2640cb2
-- title:
--   Erdos Posa: psi delete Edge of deg one
-- statement:
--   The Erdos Posa construction uses the psi delete Edge of deg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L121-L146
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L121-L146

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

theorem ErdosPosa.psi_deleteEdge_of_deg_one (hyz : H.Adj y z) (hy : deg H y = 1) :
    psi H ≤ psi (H.deleteEdges {s(y, z)}) := by sorry
