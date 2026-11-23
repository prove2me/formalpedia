-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_SigmaLog_hasDerivAt_wFactor
-- name    : Formalism.L2.Th1.F.SigmaLog.hasDerivAt_wFactor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:50.776478+00:00
-- url     : https://prove2.me/theorems/5725ee97-507b-4abf-8834-01925181add1
-- title:
--   Sigma Log: has Deriv At w Factor
-- statement:
--   The Sigma Log construction uses the has Deriv At w Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaLog.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaLog.lean#L10-L19

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaLog

theorem Formalism.L2.Th1.F.SigmaLog.hasDerivAt_wFactor (l z : ℂ) :
    HasDerivAt (wFactor l)
      (-(1 / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))
        + (1 - z / l) * (Complex.exp (z / l + z ^ 2 / (2 * l ^ 2)) * (1 / l + 2 * z / (2 * l ^ 2)))) z := by sorry
