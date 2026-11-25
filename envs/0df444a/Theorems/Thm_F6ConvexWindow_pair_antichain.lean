-- Prove2me | Theorems.Thm_F6ConvexWindow_pair_antichain
-- name    : F6ConvexWindow.pair_antichain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:08:04.687815+00:00
-- url     : https://prove2.me/theorems/831bf7b8-fa14-4a37-affb-cf11c729d276
-- title:
--   F6 Convex Window: pair antichain
-- statement:
--   Two distinct incomparable vertices give the corresponding two-element antichain.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L489-L497
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6ConvexWindow.lean#L489-L497

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem F6ConvexWindow.pair_antichain {x y : V} (hi : IncRel x y) : Antichain {x, y} := by sorry
