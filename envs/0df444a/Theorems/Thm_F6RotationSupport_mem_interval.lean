-- Prove2me | Theorems.Thm_F6RotationSupport_mem_interval
-- name    : F6RotationSupport.mem_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:47.501396+00:00
-- url     : https://prove2.me/theorems/3f2b3f9a-a414-5f10-9d55-fe1fc0fb320c
-- title:
--   F6 Rotation Support: mem interval
-- statement:
--   The F6 Rotation Support construction uses the mem interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L45-L47
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L45-L47

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.mem_interval {alpha beta rho : R} :
    rho ∈ interval alpha beta ↔ alpha ≤ rho ∧ rho ≤ beta := by sorry
