-- Prove2me | Theorems.Thm_Formalism_LT_Asm_map_subtype_injective
-- name    : Formalism.LT.Asm.map_subtype_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:06.997829+00:00
-- url     : https://prove2.me/theorems/4f701f91-49d7-4557-a8d0-bb562a955c7f
-- title:
--   Asm: map subtype injective
-- statement:
--   The Asm construction uses the map subtype injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L187-L194

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

theorem Formalism.LT.Asm.map_subtype_injective {τ : Type*} :
    Function.Injective
      (MvPowerSeries.map (unitBall K).subtype : MvPowerSeries τ (unitBall K) → MvPowerSeries τ K) := by sorry
