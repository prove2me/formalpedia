-- Prove2me | Theorems.Thm_F6RotationSupport_interval_commonInc_incomparable
-- name    : F6RotationSupport.interval_commonInc_incomparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:25:05.522837+00:00
-- url     : https://prove2.me/theorems/973c63a8-9deb-4508-b71e-fb6ddfa05bff
-- title:
--   F6 Rotation Support: interval common Inc incomparable
-- statement:
--   Human Lemma 4b: each interval rotation is incomparable with each commonInc rotation.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L121-L126
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L121-L126

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.interval_commonInc_incomparable {alpha beta a z : R}
    (ha : a ∈ interval alpha beta) (hz : z ∈ commonInc alpha beta) :
    F6ConvexWindow.IncRel a z := by sorry
