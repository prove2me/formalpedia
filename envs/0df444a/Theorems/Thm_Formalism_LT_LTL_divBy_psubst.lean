-- Prove2me | Theorems.Thm_Formalism_LT_LTL_divBy_psubst
-- name    : Formalism.LT.LTL.divBy_psubst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:51:01.750504+00:00
-- url     : https://prove2.me/theorems/015fe809-e5de-4d04-aff5-5d45cf77b534
-- title:
--   LTL: div By psubst
-- statement:
--   The LTL construction uses the div By psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L264-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L264-L273

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

theorem Formalism.LT.LTL.divBy_psubst (c : K) (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : DivBy c f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv c (f.subst P) := by sorry
