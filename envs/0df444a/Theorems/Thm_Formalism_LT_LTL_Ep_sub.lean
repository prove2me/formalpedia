-- Prove2me | Theorems.Thm_Formalism_LT_LTL_Ep_sub
-- name    : Formalism.LT.LTL.Ep_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:13.96072+00:00
-- url     : https://prove2.me/theorems/df01d9bf-43d5-4c6d-a5d8-abdd262a9266
-- title:
--   LTL: Ep sub
-- statement:
--   The LTL construction uses the Ep sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L148-L151

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
variable {K : Type u} [NormedField K] {ι : Type*}

theorem Formalism.LT.LTL.Ep_sub [Finite ι] (e' : PowerSeries K) (h0 : constantCoeff e' = 0)
    (x y : MvPowerSeries ι K) : Ep e' x - Ep e' y = Ep e' (x - y) := by sorry
