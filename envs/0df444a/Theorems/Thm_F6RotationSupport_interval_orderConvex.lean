-- Prove2me | Theorems.Thm_F6RotationSupport_interval_orderConvex
-- name    : F6RotationSupport.interval_orderConvex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:24:16.456474+00:00
-- url     : https://prove2.me/theorems/8ac2108c-bbc7-5706-af2a-2adf1f203396
-- title:
--   F6 Rotation Support: interval order Convex
-- statement:
--   Human Lemma 4a: the closed interval is order-convex.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L106-L109
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L106-L109

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.interval_orderConvex (alpha beta : R) : OrderConvex (interval alpha beta) := by sorry
