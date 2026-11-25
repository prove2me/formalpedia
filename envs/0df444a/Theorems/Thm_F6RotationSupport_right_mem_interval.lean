-- Prove2me | Theorems.Thm_F6RotationSupport_right_mem_interval
-- name    : F6RotationSupport.right_mem_interval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:25:40.191641+00:00
-- url     : https://prove2.me/theorems/bac504d0-457c-51cf-bdbb-ad56b4d7b20d
-- title:
--   F6 Rotation Support: right mem interval
-- statement:
--   The F6 Rotation Support construction uses the right mem interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L146-L147
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L146-L147

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.right_mem_interval {alpha beta : R} (hab : alpha ≤ beta) :
    beta ∈ interval alpha beta := by sorry
