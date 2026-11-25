-- Prove2me | Theorems.Thm_ErdosPosa_erdos_posa
-- name    : ErdosPosa.erdos_posa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:31:27.540367+00:00
-- url     : https://prove2.me/theorems/e37d1c10-4ac2-51b6-be0e-eb27538db65c
-- title:
--   Erdos Posa: erdos posa
-- statement:
--   The Erdős–Pósa property of cycles.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L61-L63
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L61-L63

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

theorem ErdosPosa.erdos_posa : ∃ f : ℕ → ℕ, ∀ (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V),
    HasDisjointCycles G k ∨ ∃ X : Set V, X.ncard ≤ f k ∧ IsFeedbackSet G X := by sorry
