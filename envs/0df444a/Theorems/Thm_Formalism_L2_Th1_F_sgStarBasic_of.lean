-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_sgStarBasic_of
-- name    : Formalism.L2.Th1.F.sgStarBasic_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:18.386123+00:00
-- url     : https://prove2.me/theorems/40427ac5-8010-45f7-b433-a74762eab237
-- title:
--   F: sg Star Basic of
-- statement:
--   The F construction uses the sg Star Basic of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L182-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L182-L218

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
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
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds

theorem Formalism.L2.Th1.F.sgStarBasic_of (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (h1 : SigmaSimple)
    (h3 : ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0) :
    SgStarBasic := by sorry
