-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_off
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_off
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:09.174966+00:00
-- url     : https://prove2.me/theorems/157bc7ac-227f-4471-818a-42a268a4499c
-- title:
--   Three Term Relation: three Term Quotient order off
-- statement:
--   The Three Term Relation construction uses the three Term Quotient order off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L213-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L213-L232

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_off (he : SigmaEntire) (hord : SigmaOrder) (hm : b - c ∉ L.lattice) {z : ℂ}
    (hzL : z ∉ L.lattice) {m1 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ)) :
    ((-m1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by sorry
