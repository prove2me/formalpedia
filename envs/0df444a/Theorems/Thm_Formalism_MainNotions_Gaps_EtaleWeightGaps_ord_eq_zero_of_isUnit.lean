-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq_zero_of_isUnit
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_eq_zero_of_isUnit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:07.296129+00:00
-- url     : https://prove2.me/theorems/3a30dc7f-4219-45e7-b311-3be636593ac6
-- title:
--   Etale Weight Gaps: ord eq zero of is Unit
-- statement:
--   The Etale Weight Gaps construction uses the ord eq zero of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L291-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L291-L299

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]
variable {O A}
attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR
variable {ϖ : O}

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_eq_zero_of_isUnit (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) {a : ↥(As O A)}
    (ha : IsUnit a) : ord ϖ ζ (a : A) = 0 := by sorry
