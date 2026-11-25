-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_modFun_one
-- name    : CompanionTheory.D.Upq.QuotSetU.modFun_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:46.794775+00:00
-- url     : https://prove2.me/theorems/c3bb8622-8a17-448d-aa81-2fd9ba05f2cb
-- title:
--   Quot Set U: mod Fun one
-- statement:
--   The Quot Set U construction uses the mod Fun one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/StabilizerModularFunctionTrivial.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/StabilizerModularFunctionTrivial.lean#L62-L67

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
variable {D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ}
  (hD : UnitaryGroupMassFormula.ModProps (Sset k r z) D)
include hD

theorem CompanionTheory.D.Upq.QuotSetU.modFun_one : D 1 = 1 := by sorry
