-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_expo_eq_zero_of_inW
-- name    : CompanionTheory.D.Upq.QuotSetU.expo_eq_zero_of_inW
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:42:55.266488+00:00
-- url     : https://prove2.me/theorems/8b8cb71d-5013-44e1-85e3-1c38a4645b64
-- title:
--   Quot Set U: expo eq zero of in W
-- statement:
--   The Quot Set U construction uses the expo eq zero of in W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/NContract.lean#L23-L24

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

theorem CompanionTheory.D.Upq.QuotSetU.expo_eq_zero_of_inW {i : Fin (2 * r + k + 1)} (hi : inW k r i) : expo k r i = 0 := by sorry
