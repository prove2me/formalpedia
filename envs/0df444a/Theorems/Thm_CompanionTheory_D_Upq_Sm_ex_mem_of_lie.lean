-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie
-- name    : CompanionTheory.D.Upq.Sm.ex_mem_of_lie
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:30:48.938944+00:00
-- url     : https://prove2.me/theorems/a37a218a-501e-4850-ae6e-01348ac0bc92
-- title:
--   Sm: ex mem of lie
-- statement:
--   The Sm construction uses the ex mem of lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/PhMeas.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/PhMeas.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
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
open PI.PhMeasCore
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem CompanionTheory.D.Upq.Sm.ex_mem_of_lie {Hm X : Mat n} (hX : Xᴴ * Hm + Hm * X = 0) (t : ℝ) :
    (ex X t)ᴴ * Hm * ex X t = Hm := by sorry
