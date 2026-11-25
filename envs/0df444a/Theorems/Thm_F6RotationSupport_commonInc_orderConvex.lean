-- Prove2me | Theorems.Thm_F6RotationSupport_commonInc_orderConvex
-- name    : F6RotationSupport.commonInc_orderConvex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:44:41.875199+00:00
-- url     : https://prove2.me/theorems/3f96826b-1eb2-51ed-8d21-4c7e874ccaf1
-- title:
--   F6 Rotation Support: common Inc order Convex
-- statement:
--   Human Lemma 4a: common incomparability is order-convex.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L112-L118
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L112-L118

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.commonInc_orderConvex (alpha beta : R) : OrderConvex (commonInc alpha beta) := by sorry
