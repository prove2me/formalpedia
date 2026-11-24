-- Prove2me | Theorems.Thm_Formalism_LT_LTL_coeff_lin_single
-- name    : Formalism.LT.LTL.coeff_lin_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:58.229962+00:00
-- url     : https://prove2.me/theorems/675a60ce-e0b8-41c7-a626-7a1c9dcde24e
-- title:
--   LTL: coeff lin single
-- statement:
--   The LTL construction uses the coeff lin single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L439-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L439-L442

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
variable [Fintype ι] [DecidableEq ι]

theorem Formalism.LT.LTL.coeff_lin_single (a : ι → K) (i : ι) :
    MvPowerSeries.coeff (Finsupp.single i 1) (lin a) = a i := by sorry
