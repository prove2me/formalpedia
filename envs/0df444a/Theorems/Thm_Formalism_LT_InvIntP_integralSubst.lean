-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_integralSubst
-- name    : Formalism.LT.InvIntP.integralSubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:07.018798+00:00
-- url     : https://prove2.me/theorems/84720d23-8703-4f98-b85c-9c167387dcaf
-- title:
--   Inv Int P: integral Subst
-- statement:
--   The Inv Int P construction uses the integral Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L87-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L87-L98

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
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
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem Formalism.LT.InvIntP.integralSubst (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    IntegralMv (f.subst P) := by sorry
