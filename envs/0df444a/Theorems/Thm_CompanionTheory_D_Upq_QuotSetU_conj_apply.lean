-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_conj_apply
-- name    : CompanionTheory.D.Upq.QuotSetU.conj_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:42:30.173975+00:00
-- url     : https://prove2.me/theorems/4faddd10-2f5f-4dee-9f54-4e9ddda91fef
-- title:
--   Quot Set U: conj apply
-- statement:
--   The Quot Set U construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L54-L56

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

theorem CompanionTheory.D.Upq.QuotSetU.conj_apply (t : ℝ) (g : 𝕄) (i j : Fin (2 * r + k + 1)) :
    (cdiag k r t * g * cdiag k r t⁻¹) i j = dvec t i * g i j * dvec t⁻¹ j := by sorry
