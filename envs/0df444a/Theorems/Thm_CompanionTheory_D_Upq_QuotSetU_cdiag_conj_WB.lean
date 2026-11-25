-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_conj_WB
-- name    : CompanionTheory.D.Upq.QuotSetU.cdiag_conj_WB
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:42:33.774092+00:00
-- url     : https://prove2.me/theorems/c9f4b660-ce3b-41a1-ad29-68f539dd8441
-- title:
--   Quot Set U: cdiag conj WB
-- statement:
--   The Quot Set U construction uses the cdiag conj WB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L72-L81

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

theorem CompanionTheory.D.Upq.QuotSetU.cdiag_conj_WB {t : ℝ} (ht : t ≠ 0) {a : 𝕄} (ha : WB k r a) :
    cdiag k r t * a * cdiag k r t⁻¹ = a := by sorry
