-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_nonneg_iff
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_nonneg_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:12.65027+00:00
-- url     : https://prove2.me/theorems/810fe2b4-27b2-486d-9e7a-91208f949535
-- title:
--   Etale Weight Gaps: ord At nonneg iff
-- statement:
--   The Etale Weight Gaps construction uses the ord At nonneg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L305-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L305-L324

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_nonneg_iff (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (n : ℕ) (a : ↥(As O A)) :
    0 ≤ ordAt ϖ ζ n a ↔ vL ζ ((algebraMap O ↥(As O A) ϖ) ^ n) ≤ vL ζ a := by sorry
