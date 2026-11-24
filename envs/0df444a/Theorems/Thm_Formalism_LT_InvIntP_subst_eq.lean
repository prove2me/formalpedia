-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_subst_eq
-- name    : Formalism.LT.InvIntP.subst_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:51:02.3919+00:00
-- url     : https://prove2.me/theorems/8767bed7-a323-4afe-838f-5402031158f7
-- title:
--   Inv Int P: subst eq
-- statement:
--   The Inv Int P construction uses the subst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L143-L148

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
variable {K : Type u} [NormedField K] {ι : Type v}

theorem Formalism.LT.InvIntP.subst_eq (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    {a : MvPowerSeries ι K} (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = a + a ^ 2 * (tail2 f).subst a := by sorry
