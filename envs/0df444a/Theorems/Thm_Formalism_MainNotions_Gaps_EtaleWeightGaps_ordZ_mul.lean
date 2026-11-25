-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordZ_mul
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordZ_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:01.205555+00:00
-- url     : https://prove2.me/theorems/75b3243d-d562-4edf-b665-68b518eb60f7
-- title:
--   Etale Weight Gaps: ord Z mul
-- statement:
--   The Etale Weight Gaps construction uses the ord Z mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L513-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L513-L517

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
variable {ϖ : O} (ζ : Pts O A) [IsDVRAt ζ]

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordZ_mul (h : IsUnif A ϖ) {x y : A} (hx : x ∈ nonZeroDivisors A)
    (hy : y ∈ nonZeroDivisors A) : ordZ ϖ ζ (x * y) = ordZ ϖ ζ x + ordZ ϖ ζ y := by sorry
