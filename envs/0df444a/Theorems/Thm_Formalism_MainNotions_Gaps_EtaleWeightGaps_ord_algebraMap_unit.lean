-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_algebraMap_unit
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_algebraMap_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:56.480959+00:00
-- url     : https://prove2.me/theorems/afa07cc3-8e03-49be-932a-63d7bff21b43
-- title:
--   Etale Weight Gaps: ord algebra Map unit
-- statement:
--   The Etale Weight Gaps construction uses the ord algebra Map unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L301-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L301-L303

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_algebraMap_unit (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (u : Oˣ) :
    ord ϖ ζ (algebraMap O A u) = 0 := by sorry
