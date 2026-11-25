-- Prove2me | Theorems.Thm_ErdosPosa_cyc_of_walk
-- name    : ErdosPosa.cyc_of_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:35.561985+00:00
-- url     : https://prove2.me/theorems/00b431ff-a6e0-5cb4-871f-173faeae4259
-- title:
--   Erdos Posa: cyc of walk
-- statement:
--   A cycle given by an edge `uv` and a walk from `u` to `v` avoiding that edge.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L264-L278
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L264-L278

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.cyc_of_walk {H : SimpleGraph V} {S : Set V} {u v : V} (huv : H.Adj u v) (p : H.Walk u v)
    (hS : ∀ x ∈ p.support, x ∈ S) (he : s(u, v) ∉ p.edges) : Cyc H S := by sorry
