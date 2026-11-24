-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_ballO_iff
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_ballO_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:43.548315+00:00
-- url     : https://prove2.me/theorems/b21d5193-b62b-460d-9794-a94ece7ea249
-- title:
--   Etale Weight Gaps: mem ball O iff
-- statement:
--   The Etale Weight Gaps construction uses the mem ball O iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L425-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L425-L428

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_ballO_iff [Module O V] [IsScalarTower O A V] [∀ ζ : Pts O A, IsDVRAt ζ]
    (h : IsUnif A ϖ) (he : IsGen A e) (v : V) :
    v ∈ ballO ϖ e c ↔ ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e c v := by sorry
