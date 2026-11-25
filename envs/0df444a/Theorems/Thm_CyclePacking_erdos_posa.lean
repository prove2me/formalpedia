-- Prove2me | Theorems.Thm_CyclePacking_erdos_posa
-- name    : CyclePacking.erdos_posa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:46:55.624848+00:00
-- url     : https://prove2.me/theorems/d8892857-697a-58ec-ad6a-e05cfe1a0664
-- title:
--   Cycle Packing: erdos posa
-- statement:
--   The Erdős–Pósa property of cycles.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/Solution.lean#L44-L46
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/Solution.lean#L44-L46

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Definitions.Def_ErdosPosaCycles_Solution
public import Theorems.Thm_ErdosPosa_erdos_posa

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CyclePacking
universe u

theorem CyclePacking.erdos_posa : ∃ f : ℕ → ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨ ∃ X : Set V, X.ncard ≤ f k ∧ IsFeedbackSet G X := by sorry
