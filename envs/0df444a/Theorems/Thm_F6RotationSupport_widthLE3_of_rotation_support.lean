-- Prove2me | Theorems.Thm_F6RotationSupport_widthLE3_of_rotation_support
-- name    : F6RotationSupport.widthLE3_of_rotation_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:24:00.777481+00:00
-- url     : https://prove2.me/theorems/660154b1-a1e6-4b09-b377-9c4e42b0fd26
-- title:
--   F6 Rotation Support: width LE3 of rotation support
-- statement:
--   Human Lemma 3: six men bound every antichain by counting its support fibers.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L94-L103
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L94-L103

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.widthLE3_of_rotation_support (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho) :
    F6ConvexWindow.WidthLE (V := R) 3 := by sorry
