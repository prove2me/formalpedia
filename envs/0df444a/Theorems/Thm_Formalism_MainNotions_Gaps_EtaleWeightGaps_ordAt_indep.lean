-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_indep
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_indep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:06.509743+00:00
-- url     : https://prove2.me/theorems/51f548be-2223-40c2-a689-429d09783bc5
-- title:
--   Etale Weight Gaps: ord At indep
-- statement:
--   The Etale Weight Gaps construction uses the ord At indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L166-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L166-L175

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_indep (h : IsUnif A ϖ) {x : A} {n m : ℕ} (hn : ϖ ^ n • x ∈ As O A)
    (hm : ϖ ^ m • x ∈ As O A) :
    ordAt ϖ ζ n ⟨ϖ ^ n • x, hn⟩ = ordAt ϖ ζ m ⟨ϖ ^ m • x, hm⟩ := by sorry
