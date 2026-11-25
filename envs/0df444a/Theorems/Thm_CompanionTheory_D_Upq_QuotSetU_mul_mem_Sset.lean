-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_mul_mem_Sset
-- name    : CompanionTheory.D.Upq.QuotSetU.mul_mem_Sset
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:29:31.792096+00:00
-- url     : https://prove2.me/theorems/c2b8f928-d6d8-4bc6-afae-e5e757ca9f6a
-- title:
--   Quot Set U: mul mem Sset
-- statement:
--   The Quot Set U construction uses the mul mem Sset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L132-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/SGroup.lean#L132-L142

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

theorem CompanionTheory.D.Upq.QuotSetU.mul_mem_Sset {a b : 𝕄} (ha : a ∈ Sset k r z) (hb : b ∈ Sset k r z) :
    a * b ∈ Sset k r z := by sorry
