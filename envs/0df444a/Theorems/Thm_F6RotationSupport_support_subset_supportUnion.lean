-- Prove2me | Theorems.Thm_F6RotationSupport_support_subset_supportUnion
-- name    : F6RotationSupport.support_subset_supportUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:22:36.80192+00:00
-- url     : https://prove2.me/theorems/1caa40b3-6a96-5a91-9312-6482d516f736
-- title:
--   F6 Rotation Support: support subset support Union
-- statement:
--   The F6 Rotation Support construction uses the support subset support Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L40-L43
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L40-L43

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.support_subset_supportUnion (supp : R → Finset M) {Q : Finset R}
    {rho : R} (hrho : rho ∈ Q) : supp rho ⊆ supportUnion supp Q := by sorry
