-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_Bd_mono
-- name    : Formalism.LT.CoeffP.Bd.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:43.626307+00:00
-- url     : https://prove2.me/theorems/643fa8b6-b946-4b3b-9a71-207329a959cc
-- title:
--   Bd: mono
-- statement:
--   The Bd construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L103-L105

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

theorem Formalism.LT.CoeffP.Bd.mono {a b : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (h : a ≤ b) : Bd b F := by sorry
