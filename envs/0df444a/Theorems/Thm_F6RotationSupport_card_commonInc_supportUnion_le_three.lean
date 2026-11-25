-- Prove2me | Theorems.Thm_F6RotationSupport_card_commonInc_supportUnion_le_three
-- name    : F6RotationSupport.card_commonInc_supportUnion_le_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:41:32.698067+00:00
-- url     : https://prove2.me/theorems/7cff7f55-15da-4902-8a54-6ade9d41c6d9
-- title:
--   F6 Rotation Support: card common Inc support Union le three
-- statement:
--   Human Lemma 4d: disjointness and the six-man bound leave at most three men.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L175-L188
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L175-L188

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.card_commonInc_supportUnion_le_three (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    {alpha beta : R} (hab : alpha < beta) :
    (supportUnion supp (commonInc alpha beta)).card ≤ 3 := by sorry
