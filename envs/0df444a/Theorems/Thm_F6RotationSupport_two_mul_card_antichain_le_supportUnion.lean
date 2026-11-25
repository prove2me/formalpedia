-- Prove2me | Theorems.Thm_F6RotationSupport_two_mul_card_antichain_le_supportUnion
-- name    : F6RotationSupport.two_mul_card_antichain_le_supportUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:24:01.481806+00:00
-- url     : https://prove2.me/theorems/993a7ebf-a00b-41d4-bfba-db828085ecff
-- title:
--   F6 Rotation Support: two mul card antichain le support Union
-- statement:
--   The F6 Rotation Support construction uses the two mul card antichain le support Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L82-L91
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L82-L91

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.two_mul_card_antichain_le_supportUnion (supp : R → Finset M)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    2 * A.card ≤ (supportUnion supp A).card := by sorry
