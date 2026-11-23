-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_unif_mem_nonZeroDivisors
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.unif_mem_nonZeroDivisors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:33.47444+00:00
-- url     : https://prove2.me/theorems/b8a40963-d030-49ab-83d2-7b5e093eb14c
-- title:
--   Etale Weight Gaps: unif mem non Zero Divisors
-- statement:
--   The Etale Weight Gaps construction uses the unif mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L126-L133

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.unif_mem_nonZeroDivisors (h : IsUnif A ϖ) :
    algebraMap O ↥(As O A) ϖ ∈ nonZeroDivisors ↥(As O A) := by sorry
