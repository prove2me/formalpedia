-- Prove2me | Theorems.Thm_F6RotationSupport_card_supportUnion_antichain
-- name    : F6RotationSupport.card_supportUnion_antichain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:36.426111+00:00
-- url     : https://prove2.me/theorems/f43decfb-35e3-4c47-bc57-285342b91257
-- title:
--   F6 Rotation Support: card support Union antichain
-- statement:
--   Count all actual support fibers; disjointness makes the union count exact.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L75-L80
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L75-L80

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.card_supportUnion_antichain (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    (supportUnion supp A).card = ∑ rho ∈ A, (supp rho).card := by sorry
