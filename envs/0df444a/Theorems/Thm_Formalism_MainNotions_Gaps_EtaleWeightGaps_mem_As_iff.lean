-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_As_iff
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_As_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:14.224382+00:00
-- url     : https://prove2.me/theorems/0dd180b9-eac0-42d0-9a1a-e5bc9f66bc0d
-- title:
--   Etale Weight Gaps: mem As iff
-- statement:
--   The Etale Weight Gaps construction uses the mem As iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L326-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L326-L346

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_As_iff [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (x : A) :
    x ∈ As O A ↔ ∀ ζ : Pts O A, 0 ≤ ord ϖ ζ x := by sorry
