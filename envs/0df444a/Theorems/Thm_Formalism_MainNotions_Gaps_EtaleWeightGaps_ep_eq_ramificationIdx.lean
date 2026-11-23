-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ep_eq_ramificationIdx
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ep_eq_ramificationIdx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:05.199441+00:00
-- url     : https://prove2.me/theorems/5d4c28e6-d471-464e-8b16-fc9d1732a6ab
-- title:
--   Etale Weight Gaps: ep eq ramification Idx
-- statement:
--   The Etale Weight Gaps construction uses the ep eq ramification Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L454-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L454-L461

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ep_eq_ramificationIdx {ϖ : O} (hϖ : Irreducible ϖ) (ζ : Pts O A) :
    ep ϖ ζ = ζ.asIdeal.ramificationIdx O := by sorry
