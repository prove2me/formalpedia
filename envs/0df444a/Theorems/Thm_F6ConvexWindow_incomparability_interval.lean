-- Prove2me | Theorems.Thm_F6ConvexWindow_incomparability_interval
-- name    : F6ConvexWindow.incomparability_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:33:53.685351+00:00
-- url     : https://prove2.me/theorems/36e349ce-8e78-57bc-9bd1-4f58b75d9519
-- title:
--   F6 Convex Window: incomparability interval
-- statement:
--   §8: incomparability is order-convex along a chain.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L97-L99
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L97-L99

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.incomparability_interval {x a b c : V} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : IncRel x a) (hc : IncRel x c) : IncRel x b := by sorry
