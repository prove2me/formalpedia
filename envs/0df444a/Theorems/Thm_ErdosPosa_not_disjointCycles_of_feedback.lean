-- Prove2me | Theorems.Thm_ErdosPosa_not_disjointCycles_of_feedback
-- name    : ErdosPosa.not_disjointCycles_of_feedback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:32:24.978112+00:00
-- url     : https://prove2.me/theorems/34b3a835-5c79-433b-ad26-e36fc4c96210
-- title:
--   Erdos Posa: not disjoint Cycles of feedback
-- statement:
--   A feedback vertex set of size `s` rules out `s + 1` disjoint cycles.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L73-L90
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L73-L90

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMain
public import Definitions.Def_ErdosPosaLib_ErdosPosa
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
universe u

theorem ErdosPosa.not_disjointCycles_of_feedback {V : Type u} [Finite V] (G : SimpleGraph V) {X : Set V}
    (hX : IsFeedbackSet G X) : ¬ HasDisjointCycles G (X.ncard + 1) := by sorry
