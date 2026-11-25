-- Prove2me | Theorems.Thm_F6RotationSupport_supports_disjoint_of_incomparable
-- name    : F6RotationSupport.supports_disjoint_of_incomparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:33:23.489717+00:00
-- url     : https://prove2.me/theorems/02ffd057-bbdf-5d42-b31a-c715236ae542
-- title:
--   F6 Rotation Support: supports disjoint of incomparable
-- statement:
--   HSHARE forces the actual supports of incomparable rotations to be disjoint.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L55-L62
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L55-L62

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.supports_disjoint_of_incomparable (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {rho sigma : R} (hinc : F6ConvexWindow.IncRel rho sigma) :
    Disjoint (supp rho) (supp sigma) := by sorry
