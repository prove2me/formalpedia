-- Prove2me | Theorems.Thm_Formalism_LT_Asm_integralMv_sub
-- name    : Formalism.LT.Asm.integralMv_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:01.537375+00:00
-- url     : https://prove2.me/theorems/07b5fc6b-45ce-418b-bf96-1b108773e7d4
-- title:
--   Asm: integral Mv sub
-- statement:
--   The Asm construction uses the integral Mv sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L24-L30

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.Asm.integralMv_sub {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by sorry
