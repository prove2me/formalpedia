-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_low_of_agree
-- name    : Formalism.LT.InvIntP.low_of_agree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:28.869942+00:00
-- url     : https://prove2.me/theorems/8f9cf9c3-a533-43a5-8069-92c96dde9411
-- title:
--   Inv Int P: low of agree
-- statement:
--   The Inv Int P construction uses the low of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L156-L158

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

theorem Formalism.LT.InvIntP.low_of_agree {N : ℕ} {a b : MvPowerSeries ι K} (hab : Agree N a b) : Low N (a - b) := by sorry
