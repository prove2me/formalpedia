-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordV_units_smul_gen
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_units_smul_gen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:48.065794+00:00
-- url     : https://prove2.me/theorems/235db770-3d63-5de7-8356-05dcdf70c321
-- title:
--   Etale Weight Gaps: ord V units smul gen
-- statement:
--   The Etale Weight Gaps construction uses the ord V units smul gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L562-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L562-L564

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_units_smul_gen (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (u : Aˣ)
    (v : V) : ordV ϖ ζ e c v = ord ϖ ζ (u : A) + ordV ϖ ζ ((u : A) • e) c v := by sorry
