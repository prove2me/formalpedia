-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_Bd_mul
-- name    : Formalism.LT.CoeffP.Bd.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:41.838579+00:00
-- url     : https://prove2.me/theorems/ba3d6ce1-e643-4408-951d-21db57571609
-- title:
--   Bd: mul
-- statement:
--   The Bd construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L107-L114

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
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
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem Formalism.LT.CoeffP.Bd.mul {a b : ℝ} {F G : MvPowerSeries ι K} (hF : Bd a F) (hG : Bd b G) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : Bd (a * b) (F * G) := by sorry
