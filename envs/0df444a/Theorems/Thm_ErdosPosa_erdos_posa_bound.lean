-- Prove2me | Theorems.Thm_ErdosPosa_erdos_posa_bound
-- name    : ErdosPosa.erdos_posa_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:31:39.241116+00:00
-- url     : https://prove2.me/theorems/e898e58d-b7bf-5078-9651-2aaa91025ef3
-- title:
--   Erdos Posa: erdos posa bound
-- statement:
--   **The Erdős–Pósa theorem (1965).** Some constant `c` works with `f k = c (k+1)(log₂ (k+1) + 1)`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L67-L70
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L67-L70

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

theorem ErdosPosa.erdos_posa_bound : ∃ c : ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨
      ∃ X : Set V, X.ncard ≤ c * (k + 1) * (Nat.log 2 (k + 1) + 1) ∧ IsFeedbackSet G X := by sorry
