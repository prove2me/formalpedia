-- Prove2me | Theorems.Thm_ErdosPosa_psi_deleteEdge
-- name    : ErdosPosa.psi_deleteEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:49.637875+00:00
-- url     : https://prove2.me/theorems/8b863921-5f6d-4b20-a31c-87bea5e7ecb1
-- title:
--   Erdos Posa: psi delete Edge
-- statement:
--   The Erdos Posa construction uses the psi delete Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L94-L119
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L94-L119

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

theorem ErdosPosa.psi_deleteEdge (hyz : H.Adj y z) : psi H - 2 ≤ psi (H.deleteEdges {s(y, z)}) := by sorry
