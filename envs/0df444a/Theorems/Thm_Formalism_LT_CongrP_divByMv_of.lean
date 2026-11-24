-- Prove2me | Theorems.Thm_Formalism_LT_CongrP_divByMv_of
-- name    : Formalism.LT.CongrP.divByMv_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:51:13.475247+00:00
-- url     : https://prove2.me/theorems/23ba3bdd-0752-4590-9964-c9c576e66df6
-- title:
--   Congr P: div By Mv of
-- statement:
--   The Congr P construction uses the div By Mv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L92-L93

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

theorem Formalism.LT.CongrP.divByMv_of (x : K) (φ : PowerSeries K) (h : DivBy x φ) : DivByMv x φ := by sorry
