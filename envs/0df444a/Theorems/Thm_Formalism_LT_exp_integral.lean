-- Prove2me | Theorems.Thm_Formalism_LT_exp_integral
-- name    : Formalism.LT.exp_integral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:16.441939+00:00
-- url     : https://prove2.me/theorems/a2e4aecc-e2d5-40a8-8fe4-f432f597b55b
-- title:
--   LT: exp integral
-- statement:
--   The LT construction uses the exp integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L185-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L185-L185

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
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

theorem Formalism.LT.exp_integral : Formalism.LT.ExpIntegral.{u} := by sorry
