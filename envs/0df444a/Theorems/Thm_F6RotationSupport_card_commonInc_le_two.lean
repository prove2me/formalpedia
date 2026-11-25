-- Prove2me | Theorems.Thm_F6RotationSupport_card_commonInc_le_two
-- name    : F6RotationSupport.card_commonInc_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:27:02.067426+00:00
-- url     : https://prove2.me/theorems/ed5d4d01-9e68-441e-a7cf-27d68fd92a59
-- title:
--   F6 Rotation Support: card common Inc le two
-- statement:
--   Human Lemma 4d: apply the explicit three-man capacity interface to commonInc.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L191-L202
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L191-L202

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.card_commonInc_le_two (supp : R → Finset M)
    (H6 : Fintype.card M ≤ 6)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    (HCAP3 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 3 → Q.card ≤ 2)
    {alpha beta : R} (hab : alpha < beta) :
    (commonInc alpha beta).card ≤ 2 := by sorry
