-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_normalises
-- name    : CompanionTheory.D.Upq.QuotSetU.cdiag_normalises
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:03.365151+00:00
-- url     : https://prove2.me/theorems/3161ec02-9363-47fe-8a76-79aeed552d31
-- title:
--   Quot Set U: cdiag normalises
-- statement:
--   The Quot Set U construction uses the cdiag normalises property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L107-L114

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
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

theorem CompanionTheory.D.Upq.QuotSetU.cdiag_normalises {t : ℝ} (ht : t ≠ 0) (g : 𝕄) :
    cdiag k r t * g * (cdiag k r t)⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z := by sorry
