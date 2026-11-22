-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_agree_psubst
-- name    : Formalism.LT.InvIntP.agree_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:13.285873+00:00
-- url     : https://prove2.me/theorems/7a6a8c25-308b-4859-887d-d9d5b900d7a3
-- title:
--   Inv Int P: agree psubst
-- statement:
--   The Inv Int P construction uses the agree psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L150-L154

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

theorem Formalism.LT.InvIntP.agree_psubst [Finite ι] (g : PowerSeries K) {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Agree N (g.subst a) (g.subst b) := by sorry
