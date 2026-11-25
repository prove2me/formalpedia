-- Prove2me | Theorems.Thm_F6RotationSupport_two_le_card_interval
-- name    : F6RotationSupport.two_le_card_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:26:11.725748+00:00
-- url     : https://prove2.me/theorems/bf45d9bc-e77e-50dc-a74e-76b075bf7a09
-- title:
--   F6 Rotation Support: two le card interval
-- statement:
--   Human Lemma 4c: the two distinct endpoints give at least two interval rotations.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L150-L160
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L150-L160

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.two_le_card_interval {alpha beta : R} (hab : alpha < beta) :
    2 ≤ (interval alpha beta).card := by sorry
