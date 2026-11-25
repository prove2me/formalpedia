-- Prove2me | Theorems.Thm_F6RotationSupport_interval_commonInc_supportUnion_disjoint
-- name    : F6RotationSupport.interval_commonInc_supportUnion_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:25:20.665627+00:00
-- url     : https://prove2.me/theorems/369fac1a-0b11-4b58-b115-458c44db9d28
-- title:
--   F6 Rotation Support: interval common Inc support Union disjoint
-- statement:
--   Human Lemma 4b: HSHARE makes the two support unions disjoint.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L129-L141
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L129-L141

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.interval_commonInc_supportUnion_disjoint (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (alpha beta : R) :
    Disjoint (supportUnion supp (interval alpha beta))
      (supportUnion supp (commonInc alpha beta)) := by sorry
