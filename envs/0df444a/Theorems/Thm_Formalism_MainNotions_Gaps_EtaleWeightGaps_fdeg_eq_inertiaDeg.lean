-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_fdeg_eq_inertiaDeg
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.fdeg_eq_inertiaDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:11.983651+00:00
-- url     : https://prove2.me/theorems/0927c3a3-2ad8-470d-ae3d-7d1be39deb12
-- title:
--   Etale Weight Gaps: fdeg eq inertia Deg
-- statement:
--   The Etale Weight Gaps construction uses the fdeg eq inertia Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L467-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean#L467-L478

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.fdeg_eq_inertiaDeg (ζ : Pts O A) : fdeg ζ = ζ.asIdeal.inertiaDeg O := by sorry
