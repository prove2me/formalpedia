-- Prove2me | Theorems.Thm_Formalism_LT_LTL_norm_pi_sub_pow
-- name    : Formalism.LT.LTL.norm_pi_sub_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:39:08.418397+00:00
-- url     : https://prove2.me/theorems/9445a720-760f-4542-a457-6d3e8d183caf
-- title:
--   LTL: norm pi sub pow
-- statement:
--   The LTL construction uses the norm pi sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L397-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L397-L409

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

theorem Formalism.LT.LTL.norm_pi_sub_pow {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) {r : ℕ} (hr : 2 ≤ r) :
    ‖π - π ^ r‖ = ‖π‖ := by sorry
