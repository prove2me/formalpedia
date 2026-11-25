-- Prove2me | Theorems.Thm_CyclePacking_erdos_posa_bound
-- name    : CyclePacking.erdos_posa_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:47:17.306961+00:00
-- url     : https://prove2.me/theorems/ca9cbc09-7251-4148-98e1-73b129ba41d8
-- title:
--   Cycle Packing: erdos posa bound
-- statement:
--   **The Erdős–Pósa theorem (1965).** Some constant `c` works with `f k = c (k+1)(log₂ (k+1) + 1)`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/Solution.lean#L50-L53
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/Solution.lean#L50-L53

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_ErdosPosa
public import Definitions.Def_ErdosPosaCycles_Solution
public import Theorems.Thm_ErdosPosa_erdos_posa_bound

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CyclePacking
universe u

theorem CyclePacking.erdos_posa_bound : ∃ c : ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨
      ∃ X : Set V, X.ncard ≤ c * (k + 1) * (Nat.log 2 (k + 1) + 1) ∧ IsFeedbackSet G X := by sorry
