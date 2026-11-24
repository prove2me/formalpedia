-- Prove2me | Theorems.Thm_Formalism_LT_CongrP_coeff_subst_trunc
-- name    : Formalism.LT.CongrP.coeff_subst_trunc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:57.739924+00:00
-- url     : https://prove2.me/theorems/9dd5676f-8ee6-4238-8adc-8c521b46f995
-- title:
--   Congr P: coeff subst trunc
-- statement:
--   The Congr P construction uses the coeff subst trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L36-L42

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

theorem Formalism.LT.CongrP.coeff_subst_trunc (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst (trunc (N + 1) a : PowerSeries R)) = coeff N (f.subst a) := by sorry
