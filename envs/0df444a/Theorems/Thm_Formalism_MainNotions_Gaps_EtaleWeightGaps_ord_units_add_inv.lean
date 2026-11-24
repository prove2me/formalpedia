-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_units_add_inv
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_units_add_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:34.473971+00:00
-- url     : https://prove2.me/theorems/91028f7f-bada-4fe0-8c42-30cb3d14eef3
-- title:
--   Etale Weight Gaps: ord units add inv
-- statement:
--   The Etale Weight Gaps construction uses the ord units add inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L501-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L501-L503

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_units_add_inv (h : IsUnif A ϖ) (u : Aˣ) :
    ord ϖ ζ (u : A) + ord ϖ ζ ((u⁻¹ : Aˣ) : A) = 0 := by sorry
