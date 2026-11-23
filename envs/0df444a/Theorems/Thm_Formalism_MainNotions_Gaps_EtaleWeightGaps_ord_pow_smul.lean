-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_pow_smul
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_pow_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:19.190496+00:00
-- url     : https://prove2.me/theorems/7d907562-03a5-4601-bb5c-731ab9e44c7b
-- title:
--   Etale Weight Gaps: ord pow smul
-- statement:
--   The Etale Weight Gaps construction uses the ord pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L286-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L286-L289

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_pow_smul (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (k : ℕ) (x : A) :
    ord ϖ ζ (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) : ℤ) : WithTop ℤ) + ord ϖ ζ x := by sorry
