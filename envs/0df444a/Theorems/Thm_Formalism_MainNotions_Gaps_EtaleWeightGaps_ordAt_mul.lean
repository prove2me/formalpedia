-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_mul
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:05.30902+00:00
-- url     : https://prove2.me/theorems/61d84f47-410b-441e-9c94-97baf5058929
-- title:
--   Etale Weight Gaps: ord At mul
-- statement:
--   The Etale Weight Gaps construction uses the ord At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L211-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L211-L224

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_mul (n m : ℕ) (a b : ↥(As O A)) :
    ordAt ϖ ζ (n + m) (a * b) = ordAt ϖ ζ n a + ordAt ϖ ζ m b := by sorry
