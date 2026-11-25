-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_pow_smul_coord_mem_As
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.pow_smul_coord_mem_As
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:07.57263+00:00
-- url     : https://prove2.me/theorems/45473075-c6a0-4609-b1cc-9e4bbf76b728
-- title:
--   Etale Weight Gaps: pow smul coord mem As
-- statement:
--   The Etale Weight Gaps construction uses the pow smul coord mem As property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L590-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L590-L598

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.pow_smul_coord_mem_As [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {N : ℕ} (hc : ∀ ζ, c ζ ≤ (N : ℤ)) {v : V} (hv : v ∈ ball ϖ e c) :
    ϖ ^ N • (coord e v : A) ∈ As O A := by sorry
