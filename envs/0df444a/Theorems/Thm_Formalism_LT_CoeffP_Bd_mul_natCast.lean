-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_Bd_mul_natCast
-- name    : Formalism.LT.CoeffP.Bd.mul_natCast
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:25.092882+00:00
-- url     : https://prove2.me/theorems/611ba36a-c828-4b3d-81ea-d398365c59af
-- title:
--   Bd: mul nat Cast
-- statement:
--   The Bd construction uses the mul nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L135-L139

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
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
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem Formalism.LT.CoeffP.Bd.mul_natCast {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (n : ℕ) :
    Bd (‖(n : K)‖ * a) (F * (n : MvPowerSeries ι K)) := by sorry
