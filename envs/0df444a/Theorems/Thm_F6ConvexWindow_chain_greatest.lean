-- Prove2me | Theorems.Thm_F6ConvexWindow_chain_greatest
-- name    : F6ConvexWindow.chain_greatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:05:15.28532+00:00
-- url     : https://prove2.me/theorems/122d48e0-8bc0-4332-8315-f086d45aa478
-- title:
--   F6 Convex Window: chain greatest
-- statement:
--   Every nonempty finite chain has a greatest element.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L361-L366
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L361-L366

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.chain_greatest {C : Finset V} (hc : Chain C) (hn : C.Nonempty) :
    ∃ y ∈ C, ∀ x ∈ C, x ≤ y := by sorry
