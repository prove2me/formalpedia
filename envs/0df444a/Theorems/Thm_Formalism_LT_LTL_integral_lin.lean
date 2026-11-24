-- Prove2me | Theorems.Thm_Formalism_LT_LTL_integral_lin
-- name    : Formalism.LT.LTL.integral_lin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:58.308602+00:00
-- url     : https://prove2.me/theorems/c3f79632-e685-4e0c-9940-777400711036
-- title:
--   LTL: integral lin
-- statement:
--   The LTL construction uses the integral lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L444-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L444-L449

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

theorem Formalism.LT.LTL.integral_lin (a : ι → K) (ha : ∀ i, ‖a i‖ ≤ 1) : IntegralMv (lin a) := by sorry
