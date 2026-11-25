-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_wb_of_mem_UW
-- name    : CompanionTheory.D.Upq.QuotSetU.wb_of_mem_UW
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:06.503093+00:00
-- url     : https://prove2.me/theorems/c3c91a12-30e0-5947-b6cd-bf4655496da4
-- title:
--   Quot Set U: wb of mem UW
-- statement:
--   The Quot Set U construction uses the wb of mem UW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.QuotSetU
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem CompanionTheory.D.Upq.QuotSetU.wb_of_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {h : 𝕄} (hh : h ∈ UWset k r z) : WB k r h := by sorry
