-- Prove2me | Theorems.Thm_Formalism_LT_LTL_dv_neg
-- name    : Formalism.LT.LTL.dv_neg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:51:38.623304+00:00
-- url     : https://prove2.me/theorems/ab17df2b-bbc4-46b3-944b-5c88bc51dbc6
-- title:
--   LTL: dv neg
-- statement:
--   The LTL construction uses the dv neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L201-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L201-L202

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
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
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

theorem Formalism.LT.LTL.dv_neg {c : K} {A : MvPowerSeries ι K} (hA : DivByMv c A) :
    DivByMv c (-A) := by sorry
