-- Prove2me | Theorems.Thm_Formalism_LT_Asm_map_lift
-- name    : Formalism.LT.Asm.map_lift
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:30.178801+00:00
-- url     : https://prove2.me/theorems/102b19ea-2ebb-43fa-9644-677f6fcc9d7e
-- title:
--   Asm: map lift
-- statement:
--   The Asm construction uses the map lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L181-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L181-L185

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
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
universe u
open Formalism Formalism.LT Formalism.LT.Asm
open Formalism.G
open Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.Asm.map_lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) :
    MvPowerSeries.map (unitBall K).subtype (lift F hF) = F := by sorry
