-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_nc_conj
-- name    : CompanionTheory.D.Upq.QuotSetU.nc_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:42:21.165686+00:00
-- url     : https://prove2.me/theorems/ed85bafc-f8fd-485e-b352-859a30a38633
-- title:
--   Quot Set U: nc conj
-- statement:
--   The Quot Set U construction uses the nc conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L20-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L20-L61

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

theorem CompanionTheory.D.Upq.QuotSetU.nc_conj {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1) (hm : NC k r m) :
    NC k r (a * m * b) := by sorry
