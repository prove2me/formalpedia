-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_smoothCyc_of_lowSmooth
-- name    : CompanionTheory.D.Upq.Sm.smoothCyc_of_lowSmooth
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:56:58.134804+00:00
-- url     : https://prove2.me/theorems/682c9fd4-1c5a-4d33-9a38-6ac78757604a
-- title:
--   Sm: smooth Cyc of low Smooth
-- statement:
--   The Sm construction uses the smooth Cyc of low Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L92-L100

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI.UpqRep

theorem CompanionTheory.D.Upq.Sm.smoothCyc_of_lowSmooth (hL : PI.LowSmooth) : PI.SmoothCyc := by sorry
