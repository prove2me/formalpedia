-- Prove2me | Theorems.Thm_CyclePacking_not_disjointCycles_of_feedback
-- name    : CyclePacking.not_disjointCycles_of_feedback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:36:29.501613+00:00
-- url     : https://prove2.me/theorems/cd05e167-acaa-495c-8a9e-441fa81ebfa4
-- title:
--   Cycle Packing: not disjoint Cycles of feedback
-- statement:
--   A feedback vertex set of size `s` rules out `s + 1` disjoint cycles.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/Solution.lean#L56-L58
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/Solution.lean#L56-L58

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Definitions.Def_ErdosPosaCycles_Solution
public import Theorems.Thm_ErdosPosa_not_disjointCycles_of_feedback

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CyclePacking
universe u

theorem CyclePacking.not_disjointCycles_of_feedback {V : Type u} [Finite V] (G : SimpleGraph V) {X : Set V}
    (hX : IsFeedbackSet G X) : ¬ HasDisjointCycles G (X.ncard + 1) := by sorry
