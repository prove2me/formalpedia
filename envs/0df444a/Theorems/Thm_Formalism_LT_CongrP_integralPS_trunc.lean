-- Prove2me | Theorems.Thm_Formalism_LT_CongrP_integralPS_trunc
-- name    : Formalism.LT.CongrP.integralPS_trunc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:31.125945+00:00
-- url     : https://prove2.me/theorems/6ee0a6c9-603a-478d-81af-325792dc52bb
-- title:
--   Congr P: integral PS trunc
-- statement:
--   The Congr P construction uses the integral PS trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L135-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L135-L140

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

theorem Formalism.LT.CongrP.integralPS_trunc {a : PowerSeries K} (ha : IntegralPS a) (M : ℕ) :
    IntegralPS (trunc M a : PowerSeries K) := by sorry
