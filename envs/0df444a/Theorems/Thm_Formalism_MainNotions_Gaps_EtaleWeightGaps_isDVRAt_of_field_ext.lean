-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_isDVRAt_of_field_ext
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.isDVRAt_of_field_ext
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:06.332518+00:00
-- url     : https://prove2.me/theorems/a12b0436-2415-4be4-96d0-250061b2a4fa
-- title:
--   Etale Weight Gaps: is DVRAt of field ext
-- statement:
--   The Etale Weight Gaps construction uses the is DVRAt of field ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L604-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L604-L616

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.isDVRAt_of_field_ext (K : Type*) {L : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [Algebra K L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (ζ : Pts O L) : IsDVRAt ζ := by sorry
