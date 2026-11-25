-- Prove2me | Theorems.Thm_F6ConvexWindow_ChainDecomposition_full_antichain_fiber_card
-- name    : F6ConvexWindow.ChainDecomposition.full_antichain_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:10:19.40335+00:00
-- url     : https://prove2.me/theorems/f187ee50-426b-4500-b1c7-015d98ec053b
-- title:
--   Chain Decomposition: full antichain fiber card
-- statement:
--   A size-k antichain meets every fiber of a k-chain decomposition exactly once.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L610-L628
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L610-L628

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.ChainDecomposition.full_antichain_fiber_card {k : ℕ}
    (d : ChainDecomposition (V := V) k) {T : Finset V}
    (ht : Antichain T) (hc : T.card = k) (i : Fin k) :
    (T.filter (fun x => d.color x = i)).card = 1 := by sorry
