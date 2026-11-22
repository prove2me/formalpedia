-- Prove2me | Theorems.Thm_Formalism_LT_LTL_inverseIntegralClasses_cc_s_fact
-- name    : Formalism.LT.LTL.inverseIntegralClasses_cc_s_fact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:05.332721+00:00
-- url     : https://prove2.me/theorems/5e4957e1-0839-456b-b31c-08aeaa5ce4b3
-- title:
--   LTL: inverse Integral Classes cc s fact
-- statement:
--   The LTL construction uses the inverse Integral Classes cc s fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L144-L146

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

theorem Formalism.LT.LTL.inverseIntegralClasses_cc_s_fact (e' : PowerSeries K) (h0 : constantCoeff e' = 0) (i : ι) :
    MvPowerSeries.constantCoeff (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) = 0 := by sorry
