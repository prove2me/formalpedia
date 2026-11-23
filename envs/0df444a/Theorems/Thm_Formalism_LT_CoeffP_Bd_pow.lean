-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_Bd_pow
-- name    : Formalism.LT.CoeffP.Bd.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:28.26001+00:00
-- url     : https://prove2.me/theorems/562d8c16-f709-473c-89cf-17dfd0609960
-- title:
--   Bd: pow
-- statement:
--   The Bd construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L122-L127

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

theorem Formalism.LT.CoeffP.Bd.pow {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (ha : 0 ≤ a) :
    ∀ n : ℕ, Bd (a ^ n) (F ^ n)
  := by sorry
