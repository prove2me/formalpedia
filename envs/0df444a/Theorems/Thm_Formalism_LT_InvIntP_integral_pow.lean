-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_integral_pow
-- name    : Formalism.LT.InvIntP.integral_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:30.953799+00:00
-- url     : https://prove2.me/theorems/dbb8dfd6-e89e-41a8-8b60-48d2c8c9f067
-- title:
--   Inv Int P: integral pow
-- statement:
--   The Inv Int P construction uses the integral pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L77-L85

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem Formalism.LT.InvIntP.integral_pow {A : MvPowerSeries ι K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv (A ^ n) := by sorry
