-- Prove2me | Theorems.Thm_F6ConvexWindow_Ak_zero
-- name    : F6ConvexWindow.Ak_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:35:36.632524+00:00
-- url     : https://prove2.me/theorems/aa5cbd63-0bcf-470c-b7ff-49c2d4a13dd1
-- title:
--   F6 Convex Window: Ak zero
-- statement:
--   §6: the unique zero-element antichain.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L436-L447
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L436-L447

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.Ak_zero : Ak (V := V) 0 = 1 := by sorry
