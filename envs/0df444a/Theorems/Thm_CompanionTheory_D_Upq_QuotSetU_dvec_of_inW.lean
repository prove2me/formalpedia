-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_dvec_of_inW
-- name    : CompanionTheory.D.Upq.QuotSetU.dvec_of_inW
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:42:09.640567+00:00
-- url     : https://prove2.me/theorems/89058ab4-deab-54bf-b6d9-469c459f29b6
-- title:
--   Quot Set U: dvec of in W
-- statement:
--   The Quot Set U construction uses the dvec of in W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L40-L41

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

theorem CompanionTheory.D.Upq.QuotSetU.dvec_of_inW {t : ℝ} {i : Fin (2 * r + k + 1)} (hi : inW k r i) : dvec (k := k) (r := r) t i = 1 := by sorry
