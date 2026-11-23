-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_Low_sub
-- name    : Formalism.LT.InvIntP.Low.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:08.088969+00:00
-- url     : https://prove2.me/theorems/e9ced174-3c70-483e-8d00-be5df6c26375
-- title:
--   Low: sub
-- statement:
--   The Low construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L41-L44

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

theorem Formalism.LT.InvIntP.Low.sub {m : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low m y) :
    Low m (x - y) := by sorry
