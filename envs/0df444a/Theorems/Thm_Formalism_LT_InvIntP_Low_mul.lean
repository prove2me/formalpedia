-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_Low_mul
-- name    : Formalism.LT.InvIntP.Low.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:48.656507+00:00
-- url     : https://prove2.me/theorems/b7dd91fb-c148-4549-be39-fe11955e60df
-- title:
--   Low: mul
-- statement:
--   The Low construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L24-L34

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_G_LogCR_Agree_mul

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

theorem Formalism.LT.InvIntP.Low.mul {m k : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) (x * y) := by sorry
