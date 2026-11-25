-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Hunt_integralClosure_dvr
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.integralClosure_dvr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:14.260974+00:00
-- url     : https://prove2.me/theorems/6682369a-e633-4ab7-9060-23245f47b570
-- title:
--   Hunt: integral Closure dvr
-- statement:
--   The Hunt construction uses the integral Closure dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/IsIntegralOfAll.lean#L58-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/IsIntegralOfAll.lean#L58-L165

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_IsIntegralOfAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.integralClosure_dvr :
    ∀ (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A]
    [FiniteDimensional K A] [IsReduced A],
    Module.Finite O ↥(As O A) ∧ ∀ ζ : Pts O A, IsDVRAt ζ := by sorry
