-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_shift
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_shift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:26.966011+00:00
-- url     : https://prove2.me/theorems/96d7d257-b688-42ac-b64d-34ccec9b9aa4
-- title:
--   Etale Weight Gaps: ord At shift
-- statement:
--   The Etale Weight Gaps construction uses the ord At shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L151-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L151-L164

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_shift (h : IsUnif A ϖ) (n k : ℕ) (a : ↥(As O A)) :
    ordAt ϖ ζ (n + k) ((algebraMap O ↥(As O A) ϖ) ^ k * a) = ordAt ϖ ζ n a := by sorry
