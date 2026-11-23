-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_eq_twistedGamma_of_sigmaZero
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.threeTermNum_eq_twistedGamma_of_sigmaZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:10.781889+00:00
-- url     : https://prove2.me/theorems/167bd7e9-7ffa-4b72-ad20-ab047ae7f993
-- title:
--   Three Term Relation: three Term Num eq twisted Gamma of sigma Zero
-- statement:
--   The Three Term Relation construction uses the three Term Num eq twisted Gamma of sigma Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L71-L78

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThreeTermRelation
variable (L : PeriodPair) (b c : ℂ)

theorem Formalism.L2.Th1.F.ThreeTermRelation.threeTermNum_eq_twistedGamma_of_sigmaZero (hz : SigmaZero) (x : ℂ) (hx : x ≠ 0) : nAux L b c x = frobeniusStickelbergerDetMulSigmaCube L b c x := by sorry
