-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_isUnif_of_field
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.isUnif_of_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:18.126918+00:00
-- url     : https://prove2.me/theorems/eaf776f9-0cbd-40a8-bba9-dd5c30148ef9
-- title:
--   Etale Weight Gaps: is Unif of field
-- statement:
--   The Etale Weight Gaps construction uses the is Unif of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L66-L82

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.isUnif_of_field (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra K A]
    [IsScalarTower O K A] [Algebra.IsIntegral K A] {ϖ : O} (hϖ : Irreducible ϖ) : IsUnif A ϖ := by sorry
