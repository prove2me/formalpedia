-- Prove2me | Theorems.Thm_Formalism_LT_LTL_Ldef_zero
-- name    : Formalism.LT.LTL.Ldef_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:52.558542+00:00
-- url     : https://prove2.me/theorems/6f1004c3-9821-46cc-ad42-0db425541606
-- title:
--   LTL: Ldef zero
-- statement:
--   The LTL construction uses the Ldef zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L423-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L423-L426

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

theorem Formalism.LT.LTL.Ldef_zero [Finite ι] (e e' : PowerSeries K) (he0 : constantCoeff e = 0)
    (he'0 : constantCoeff e' = 0) : Ldef e e' (0 : MvPowerSeries ι K) = 0 := by sorry
