-- Prove2me | Theorems.Thm_Formalism_LT_expIntegral
-- name    : Formalism.LT.expIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:41.534716+00:00
-- url     : https://prove2.me/theorems/5792d885-81fe-424a-a11e-8e7b60712cee
-- title:
--   LT: exp Integral
-- statement:
--   The LT construction uses the exp Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/LubinTateExample.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/LubinTateExample.lean#L45-L45

import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SolveExistsProof
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Theorems.Thm_Formalism_LT_ExpP_expIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LT
universe u v

theorem Formalism.LT.expIntegral : ExpIntegral.{u} := by sorry
