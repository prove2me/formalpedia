-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_mem_Sset_iff
-- name    : CompanionTheory.D.Upq.QuotSetU.mem_Sset_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:18.266921+00:00
-- url     : https://prove2.me/theorems/b9bc7a29-e213-4f88-8ff1-15c5f2c2db06
-- title:
--   Quot Set U: mem Sset iff
-- statement:
--   The Quot Set U construction uses the mem Sset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L95-L103

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
variable {z : Fin (2 * r + k + 1) → ℂ}

theorem CompanionTheory.D.Upq.QuotSetU.mem_Sset_iff (g : 𝕄) : g ∈ Sset k r z ↔ ∃ h ∈ UWset k r z, h⁻¹ * g ∈ Nset k r := by sorry
