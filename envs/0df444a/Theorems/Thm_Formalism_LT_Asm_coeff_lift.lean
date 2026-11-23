-- Prove2me | Theorems.Thm_Formalism_LT_Asm_coeff_lift
-- name    : Formalism.LT.Asm.coeff_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:25.669416+00:00
-- url     : https://prove2.me/theorems/b9a302ae-cb67-4bda-816a-d60a26b62a4b
-- title:
--   Asm: coeff lift
-- statement:
--   The Asm construction uses the coeff lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L178-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L178-L179

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

theorem Formalism.LT.Asm.coeff_lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) (d : τ →₀ ℕ) :
    ((MvPowerSeries.coeff d (lift F hF) : unitBall K) : K) = MvPowerSeries.coeff d F := by sorry
