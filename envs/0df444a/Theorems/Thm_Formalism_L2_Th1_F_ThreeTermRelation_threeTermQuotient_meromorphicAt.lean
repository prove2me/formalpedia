-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_meromorphicAt
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_meromorphicAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:17.714465+00:00
-- url     : https://prove2.me/theorems/7c0d1c71-639f-46a8-acd1-e5eabc47b0fb
-- title:
--   Three Term Relation: three Term Quotient meromorphic At
-- statement:
--   The Three Term Relation construction uses the three Term Quotient meromorphic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L144-L145

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (threeTermQuotient L b c) z := by sorry
