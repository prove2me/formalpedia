-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_inv_mem_Sset
-- name    : CompanionTheory.D.Upq.QuotSetU.inv_mem_Sset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:13.414696+00:00
-- url     : https://prove2.me/theorems/958c6aca-0bd0-4cdf-a00c-0ff815458ad5
-- title:
--   Quot Set U: inv mem Sset
-- statement:
--   The Quot Set U construction uses the inv mem Sset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L144-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L144-L153

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

theorem CompanionTheory.D.Upq.QuotSetU.inv_mem_Sset {a : 𝕄} (ha : a ∈ Sset k r z) : a⁻¹ ∈ Sset k r z := by sorry
