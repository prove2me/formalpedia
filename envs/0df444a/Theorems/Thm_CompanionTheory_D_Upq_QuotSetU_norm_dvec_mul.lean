-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_norm_dvec_mul
-- name    : CompanionTheory.D.Upq.QuotSetU.norm_dvec_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:42:17.180054+00:00
-- url     : https://prove2.me/theorems/6f331fcb-a1ad-545c-8041-b35e59e7faa3
-- title:
--   Quot Set U: norm dvec mul
-- statement:
--   The Quot Set U construction uses the norm dvec mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L116-L121

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

theorem CompanionTheory.D.Upq.QuotSetU.norm_dvec_mul (t : ℝ) (ht : 0 < t) (x : ℂ) (i j : Fin (2 * r + k + 1)) :
    ‖dvec (k := k) (r := r) t i * x * dvec t⁻¹ j‖ = t ^ (expo k r i - expo k r j) * ‖x‖ := by sorry
