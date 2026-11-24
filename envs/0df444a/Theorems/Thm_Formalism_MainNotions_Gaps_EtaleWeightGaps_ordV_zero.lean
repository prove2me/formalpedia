-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordV_zero
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:07.198855+00:00
-- url     : https://prove2.me/theorems/315ab7ba-7cd5-48e3-a149-030f7afaa27e
-- title:
--   Etale Weight Gaps: ord V zero
-- statement:
--   The Etale Weight Gaps construction uses the ord V zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L399-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L399-L401

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
variable {V : Type*} [AddCommGroup V] [Module A V]
variable {ϖ : O} {e : V} (c : Pts O A → ℤ)

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_zero (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) :
    ordV ϖ ζ e c 0 = ⊤ := by sorry
