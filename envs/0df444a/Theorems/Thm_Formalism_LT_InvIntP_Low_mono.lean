-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_Low_mono
-- name    : Formalism.LT.InvIntP.Low.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:09.858223+00:00
-- url     : https://prove2.me/theorems/28bc8bac-d9cd-42e7-9114-bcf134443ebd
-- title:
--   Low: mono
-- statement:
--   The Low construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L21-L22

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_G_LogCR_Agree_mono

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

theorem Formalism.LT.InvIntP.Low.mono {m k : ℕ} {x : MvPowerSeries ι K} (h : Low m x) (hk : k ≤ m) : Low k x := by sorry
