-- Prove2me | Theorems.Thm_ErdosPosa_deg_deleteEdge_other
-- name    : ErdosPosa.deg_deleteEdge_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:31.350161+00:00
-- url     : https://prove2.me/theorems/aa946e4d-0060-5f8e-a000-eacd20c64a4e
-- title:
--   Erdos Posa: deg delete Edge other
-- statement:
--   The Erdos Posa construction uses the deg delete Edge other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L80-L90
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L80-L90

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

theorem ErdosPosa.deg_deleteEdge_other (v : V) (hvy : v ≠ y) (hvz : v ≠ z) :
    deg (H.deleteEdges {s(y, z)}) v = deg H v := by sorry
