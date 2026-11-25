-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_mul
-- name    : CompanionTheory.D.Upq.QuotSetU.cdiag_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:42:00.028492+00:00
-- url     : https://prove2.me/theorems/8c4915b4-a66a-5ea9-8582-ae6a880baaed
-- title:
--   Quot Set U: cdiag mul
-- statement:
--   The Quot Set U construction uses the cdiag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L43-L45

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

theorem CompanionTheory.D.Upq.QuotSetU.cdiag_mul {t : ℝ} (ht : t ≠ 0) : cdiag k r t * cdiag k r t⁻¹ = 1 := by sorry
