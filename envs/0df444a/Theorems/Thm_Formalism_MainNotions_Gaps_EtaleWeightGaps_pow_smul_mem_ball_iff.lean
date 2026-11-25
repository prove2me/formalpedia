-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_pow_smul_mem_ball_iff
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.pow_smul_mem_ball_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:27.021574+00:00
-- url     : https://prove2.me/theorems/aec255ce-a08a-4e68-ad4e-7b694c221a98
-- title:
--   Etale Weight Gaps: pow smul mem ball iff
-- statement:
--   The Etale Weight Gaps construction uses the pow smul mem ball iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L441-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L441-L448

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.pow_smul_mem_ball_iff [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    (k : ℕ) (v : V) :
    (algebraMap O A ϖ) ^ k • v ∈ ball ϖ e c ↔
      v ∈ ball ϖ e (fun ζ => c ζ + (k : ℤ) * (ep ϖ ζ : ℤ)) := by sorry
