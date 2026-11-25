-- Prove2me | Theorems.Thm_ErdosPosa_deg_deleteEdge_right
-- name    : ErdosPosa.deg_deleteEdge_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:26.75896+00:00
-- url     : https://prove2.me/theorems/d30e0e68-7b3b-5d56-851c-3a93210c2c1e
-- title:
--   Erdos Posa: deg delete Edge right
-- statement:
--   The Erdos Posa construction uses the deg delete Edge right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L74-L77
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L74-L77

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

theorem ErdosPosa.deg_deleteEdge_right (hyz : H.Adj y z) :
    deg (H.deleteEdges {s(y, z)}) z = deg H z - 1 := by sorry
