-- Prove2me | Theorems.Thm_Formalism_LT_PadicP_map_coe_injective_mv
-- name    : Formalism.LT.PadicP.map_coe_injective_mv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:57.966669+00:00
-- url     : https://prove2.me/theorems/c7b612d1-dec5-420e-b82c-4c669a14dcb5
-- title:
--   Padic P: map coe injective mv
-- statement:
--   The Padic P construction uses the map coe injective mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/IsHomOfSubstEqSmul.lean#L180-L183

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G

theorem Formalism.LT.PadicP.map_coe_injective_mv {p : ℕ} [Fact p.Prime] {σ : Type} :
    Function.Injective (MvPowerSeries.map (σ := σ) (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])) := by sorry
