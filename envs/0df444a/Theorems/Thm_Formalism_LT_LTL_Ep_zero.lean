-- Prove2me | Theorems.Thm_Formalism_LT_LTL_Ep_zero
-- name    : Formalism.LT.LTL.Ep_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:44.153668+00:00
-- url     : https://prove2.me/theorems/94bee5ef-75d9-4c56-a3ec-5708c9bdb214
-- title:
--   LTL: Ep zero
-- statement:
--   The LTL construction uses the Ep zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L417-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L417-L421

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

theorem Formalism.LT.LTL.Ep_zero [Finite ι] (e' : PowerSeries K) (he'0 : constantCoeff e' = 0) :
    Ep e' (0 : MvPowerSeries ι K) = 0 := by sorry
