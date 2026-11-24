-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_add
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:07.61685+00:00
-- url     : https://prove2.me/theorems/08bc24c5-0a4f-4d2b-b274-a2803d694d39
-- title:
--   Etale Weight Gaps: ord At add
-- statement:
--   The Etale Weight Gaps construction uses the ord At add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L236-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L236-L243

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
variable (ζ : Pts O A) [IsDVRAt ζ]

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_add (n : ℕ) (a b : ↥(As O A)) :
    min (ordAt ϖ ζ n a) (ordAt ϖ ζ n b) ≤ ordAt ϖ ζ n (a + b) := by sorry
