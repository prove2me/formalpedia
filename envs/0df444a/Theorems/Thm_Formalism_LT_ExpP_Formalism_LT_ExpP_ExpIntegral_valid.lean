-- Prove2me | Theorems.Thm_Formalism_LT_ExpP_Formalism_LT_ExpP_ExpIntegral_valid
-- name    : Formalism.LT.ExpP.Formalism.LT.ExpP.ExpIntegral_valid
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:23.980726+00:00
-- url     : https://prove2.me/theorems/1d8aa7a6-310b-5349-b7e5-1af5e329dc19
-- title:
--   Exp P: Exp Integral valid
-- statement:
--   The Exp P construction uses the Exp Integral valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L179-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L179-L179

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
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.ExpP.Formalism.LT.ExpP.ExpIntegral_valid : Formalism.LT.ExpIntegral.{u} := by sorry
