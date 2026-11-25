-- Prove2me | Theorems.Thm_F6RotationSupport_mem_commonInc
-- name    : F6RotationSupport.mem_commonInc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:32:23.138662+00:00
-- url     : https://prove2.me/theorems/e837f81a-8a15-51fc-aace-43756e2355ea
-- title:
--   F6 Rotation Support: mem common Inc
-- statement:
--   The F6 Rotation Support construction uses the mem common Inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L49-L52
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L49-L52

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.mem_commonInc {alpha beta rho : R} :
    rho ∈ commonInc alpha beta ↔
      F6ConvexWindow.IncRel alpha rho ∧ F6ConvexWindow.IncRel beta rho := by sorry
