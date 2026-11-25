-- Prove2me | Theorems.Thm_F6RotationSupport_three_le_card_interval_supportUnion
-- name    : F6RotationSupport.three_le_card_interval_supportUnion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:26:50.984028+00:00
-- url     : https://prove2.me/theorems/c39ddaef-28c9-44fe-a923-d47012597bc7
-- title:
--   F6 Rotation Support: three le card interval support Union
-- statement:
--   Human Lemma 4c: apply the explicit two-man capacity interface to the interval.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L163-L172
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L163-L172

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.three_le_card_interval_supportUnion (supp : R → Finset M)
    (HCAP2 : ∀ Q : Finset R, OrderConvex Q →
      (supportUnion supp Q).card ≤ 2 → Q.card ≤ 1)
    {alpha beta : R} (hab : alpha < beta) :
    3 ≤ (supportUnion supp (interval alpha beta)).card := by sorry
