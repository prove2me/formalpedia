-- Prove2me | Theorems.Thm_ErdosPosa_deg_deleteEdge_left
-- name    : ErdosPosa.deg_deleteEdge_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:46.477697+00:00
-- url     : https://prove2.me/theorems/874b5246-de19-4650-8fbe-e1cf76ae3061
-- title:
--   Erdos Posa: deg delete Edge left
-- statement:
--   The Erdos Posa construction uses the deg delete Edge left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L68-L71
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L68-L71

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

theorem ErdosPosa.deg_deleteEdge_left (hyz : H.Adj y z) :
    deg (H.deleteEdges {s(y, z)}) y = deg H y - 1 := by sorry
