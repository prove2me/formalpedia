-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_isCompact_nearOne
-- name    : CompanionTheory.D.Upq.QuotSetU.isCompact_nearOne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:03.533744+00:00
-- url     : https://prove2.me/theorems/9d0feca6-3415-46a1-bb3f-08378ff05f15
-- title:
--   Quot Set U: is Compact near One
-- statement:
--   The Quot Set U construction uses the is Compact near One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/StabilizerModularFunctionTrivial.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/StabilizerModularFunctionTrivial.lean#L38-L54

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

theorem CompanionTheory.D.Upq.QuotSetU.isCompact_nearOne (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsCompact {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} := by sorry
