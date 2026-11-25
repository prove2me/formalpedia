-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_pow_mem_Sset
-- name    : CompanionTheory.D.Upq.QuotSetU.pow_mem_Sset
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:07.829325+00:00
-- url     : https://prove2.me/theorems/91b50e05-bcd1-4452-a62e-c40112d06643
-- title:
--   Quot Set U: pow mem Sset
-- statement:
--   The Quot Set U construction uses the pow mem Sset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/StabilizerModularFunctionTrivial.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/StabilizerModularFunctionTrivial.lean#L14-L17

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_StabilizerModularFunctionTrivial
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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem CompanionTheory.D.Upq.QuotSetU.pow_mem_Sset {x : 𝕄} (hx : x ∈ Sset k r z) (p : ℕ) : x ^ p ∈ Sset k r z := by sorry
