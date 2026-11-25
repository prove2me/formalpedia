-- Prove2me | Theorems.Thm_F6RotationSupport_widthLE3_and_ci2_of_rotation_support
-- name    : F6RotationSupport.widthLE3_and_ci2_of_rotation_support
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T11:19:11.896276+00:00
-- url     : https://prove2.me/theorems/e4007818-047c-43ac-8ab0-933f25131999
-- title:
--   F6 Rotation Support: width LE3 and ci2 of rotation support
-- statement:
--   The complete support/poset bridge under exactly the five specified hypotheses.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L245-L256
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L245-L256

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.widthLE3_and_ci2_of_rotation_support (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2) :
    F6ConvexWindow.WidthLE (V := R) 3 ∧ F6ConvexWindow.CI2 (V := R) := by sorry
