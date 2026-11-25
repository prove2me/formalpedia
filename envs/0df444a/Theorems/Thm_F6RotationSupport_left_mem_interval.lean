-- Prove2me | Theorems.Thm_F6RotationSupport_left_mem_interval
-- name    : F6RotationSupport.left_mem_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:25:41.071882+00:00
-- url     : https://prove2.me/theorems/7a2c0d4a-be62-4d40-8f3a-bbab7c99913c
-- title:
--   F6 Rotation Support: left mem interval
-- statement:
--   The F6 Rotation Support construction uses the left mem interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L143-L144
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L143-L144

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.left_mem_interval {alpha beta : R} (hab : alpha ≤ beta) :
    alpha ∈ interval alpha beta := by sorry
