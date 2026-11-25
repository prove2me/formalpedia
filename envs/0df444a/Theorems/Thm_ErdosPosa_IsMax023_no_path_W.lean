-- Prove2me | Theorems.Thm_ErdosPosa_IsMax023_no_path_W
-- name    : ErdosPosa.IsMax023.no_path_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:17.013571+00:00
-- url     : https://prove2.me/theorems/f6630b7a-adb4-4b9d-9fb0-eaef956de213
-- title:
--   Is Max023: no path W
-- statement:
--   No `H`-avoiding connection between two distinct degree-2 vertices through `R`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L116-L177
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L116-L177

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}

theorem ErdosPosa.IsMax023.no_path_W (hH : IsMax023 G H) {w1 w2 : V} (hw1 : deg H w1 = 2)
    (hw2 : deg H w2 = 2) (hne : w1 ≠ w2) (p : G.Walk w1 w2)
    (hsupp : ∀ x ∈ p.support, x = w1 ∨ x = w2 ∨ deg H x = 0)
    (hedges : ∀ e ∈ p.edges, e ∉ H.edgeSet) : False := by sorry
