-- Prove2me | Theorems.Thm_ErdosPosa_cyc_glue
-- name    : ErdosPosa.cyc_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:29.943382+00:00
-- url     : https://prove2.me/theorems/40d8fe5d-f527-448d-961c-74d8646b012a
-- title:
--   Erdos Posa: cyc glue
-- statement:
--   Gluing two vertex sets along at most one vertex: a cycle in the union lies in one part.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L164-L235
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L164-L235

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.cyc_glue {H : SimpleGraph V} {X Y : Set V} (h : Cyc H (X ∪ Y))
    (hcross : ∀ a b, a ∈ X → a ∉ Y → b ∈ Y → b ∉ X → ¬ H.Adj a b)
    (hint : ∀ a b, a ∈ X → a ∈ Y → b ∈ X → b ∈ Y → a = b) : Cyc H X ∨ Cyc H Y := by sorry
