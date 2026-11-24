-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_InvIntegralOfClass_proof
-- name    : Formalism.LT.InvIntP.InvIntegralOfClass_proof
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:08.010721+00:00
-- url     : https://prove2.me/theorems/4281f1fb-d53f-47bd-8264-b280b9ffe306
-- title:
--   Inv Int P: Inv Integral Of Class proof
-- statement:
--   The Inv Int P construction uses the Inv Integral Of Class proof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L238-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L238-L240

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

theorem Formalism.LT.InvIntP.InvIntegralOfClass_proof : Formalism.LT.InvIntegralOfClass.{u, v} := by sorry
