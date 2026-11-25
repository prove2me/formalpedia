-- Prove2me | Theorems.Thm_ErdosPosa_cyc_remove_low
-- name    : ErdosPosa.cyc_remove_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:10.812149+00:00
-- url     : https://prove2.me/theorems/f088a0f4-8f6a-44c0-8ace-b14df8d53296
-- title:
--   Erdos Posa: cyc remove low
-- statement:
--   Removing a vertex with at most one neighbour inside `S` preserves having a cycle in `S`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L112-L161
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L112-L161

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.cyc_remove_low {H : SimpleGraph V} {S : Set V} {x : V} (h : Cyc H S)
    (hx : ∀ y z, y ∈ S → z ∈ S → H.Adj x y → H.Adj x z → y = z) : Cyc H (S \ {x}) := by sorry
