-- Prove2me | Theorems.Thm_Formalism_LT_CongrP_integralMv_of
-- name    : Formalism.LT.CongrP.integralMv_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:51:22.473789+00:00
-- url     : https://prove2.me/theorems/d61495e2-e574-4aa2-a3e8-1a479345c6f4
-- title:
--   Congr P: integral Mv of
-- statement:
--   The Congr P construction uses the integral Mv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L89-L90

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
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
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.CongrP.integralMv_of (φ : PowerSeries K) (h : IntegralPS φ) : IntegralMv φ := by sorry
