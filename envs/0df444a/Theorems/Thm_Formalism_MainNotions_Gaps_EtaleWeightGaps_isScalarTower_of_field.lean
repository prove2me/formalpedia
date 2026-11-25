-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_isScalarTower_of_field
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.isScalarTower_of_field
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:09.247356+00:00
-- url     : https://prove2.me/theorems/2760000a-0118-47a0-a502-05f8687487ae
-- title:
--   Etale Weight Gaps: is Scalar Tower of field
-- statement:
--   The Etale Weight Gaps construction uses the is Scalar Tower of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L537-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L537-L541

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
variable {V : Type*} [AddCommGroup V] [Module A V] {ϖ : O} {e : V} (c : Pts O A → ℤ)

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.isScalarTower_of_field (K : Type*) [Field K] [Algebra O K] [Algebra K A]
    [IsScalarTower O K A] [Module K V] [IsScalarTower K A V] [Module O V] [IsScalarTower O K V] :
    IsScalarTower O A V := by sorry
