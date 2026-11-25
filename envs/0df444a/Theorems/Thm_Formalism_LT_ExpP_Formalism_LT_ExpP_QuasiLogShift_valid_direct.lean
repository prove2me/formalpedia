-- Prove2me | Theorems.Thm_Formalism_LT_ExpP_Formalism_LT_ExpP_QuasiLogShift_valid_direct
-- name    : Formalism.LT.ExpP.Formalism.LT.ExpP.QuasiLogShift_valid_direct
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:35.443437+00:00
-- url     : https://prove2.me/theorems/9ff26d67-fa8b-4213-9eed-0b04bd444eab
-- title:
--   Exp P: Quasi Log Shift valid direct
-- statement:
--   The Exp P construction uses the Quasi Log Shift valid direct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L181-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L181-L181

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

theorem Formalism.LT.ExpP.Formalism.LT.ExpP.QuasiLogShift_valid_direct : Formalism.LT.QuasiLogShift.{u} := by sorry
