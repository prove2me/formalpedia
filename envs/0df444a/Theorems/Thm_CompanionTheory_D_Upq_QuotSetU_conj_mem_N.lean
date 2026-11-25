-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_conj_mem_N
-- name    : CompanionTheory.D.Upq.QuotSetU.conj_mem_N
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:19.950835+00:00
-- url     : https://prove2.me/theorems/883deaf3-df2c-4ed4-adc7-2e3c779ece5e
-- title:
--   Quot Set U: conj mem N
-- statement:
--   The Quot Set U construction uses the conj mem N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L63-L67

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

theorem CompanionTheory.D.Upq.QuotSetU.conj_mem_N {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1)
    (haU : a ∈ UH (Hpk k r)) (hbU : b ∈ UH (Hpk k r)) (hm : m ∈ Nset k r) :
    a * m * b ∈ Nset k r := by sorry
