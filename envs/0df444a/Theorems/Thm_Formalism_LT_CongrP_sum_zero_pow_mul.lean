-- Prove2me | Theorems.Thm_Formalism_LT_CongrP_sum_zero_pow_mul
-- name    : Formalism.LT.CongrP.sum_zero_pow_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:51:11.440859+00:00
-- url     : https://prove2.me/theorems/b3bcf7f6-2e68-496d-8231-a7a8ce4ec486
-- title:
--   Congr P: sum zero pow mul
-- statement:
--   The Congr P construction uses the sum zero pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L44-L50

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
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
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {R : Type*} [CommRing R]

theorem Formalism.LT.CongrP.sum_zero_pow_mul (n : ℕ) :
    ∑ i ∈ Finset.range n, (0 : R) ^ i * (0 : R) ^ (n - 1 - i) = if n = 1 then 1 else 0 := by sorry
