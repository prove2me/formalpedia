-- Prove2me | Theorems.Thm_F6RotationSupport_ci2_of_rotation_support
-- name    : F6RotationSupport.ci2_of_rotation_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:27:15.825747+00:00
-- url     : https://prove2.me/theorems/cdf82bc8-0d1b-4f84-80f6-e2f87736bec6
-- title:
--   F6 Rotation Support: ci2 of rotation support
-- statement:
--   Human Lemma 4, packaged as exactly the parent's CI2 predicate.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L230-L242
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L230-L242

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.ci2_of_rotation_support (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2) :
    F6ConvexWindow.CI2 (V := R) := by sorry
