-- Prove2me | Theorems.Thm_F6RotationSupport_antichain_supports_pairwiseDisjoint
-- name    : F6RotationSupport.antichain_supports_pairwiseDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:06.532787+00:00
-- url     : https://prove2.me/theorems/f9948f0a-70a5-43d8-9dd0-ce96d39ecd84
-- title:
--   F6 Rotation Support: antichain supports pairwise Disjoint
-- statement:
--   Distinct elements of any antichain index pairwise-disjoint support fibers.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L65-L72
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L65-L72

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.antichain_supports_pairwiseDisjoint (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    (A : Set R).PairwiseDisjoint supp := by sorry
