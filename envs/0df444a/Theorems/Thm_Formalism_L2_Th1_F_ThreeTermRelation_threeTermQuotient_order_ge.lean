-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_ge
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:18.225334+00:00
-- url     : https://prove2.me/theorems/ffe2f600-a0b2-45f1-8036-71f6c2208369
-- title:
--   Three Term Relation: three Term Quotient order ge
-- statement:
--   The Three Term Relation construction uses the three Term Quotient order ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L176-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L176-L193

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_ge (he : SigmaEntire) {z : ℂ} {k m1 m2 m3 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ))
    (h2 : meromorphicOrderAt (fun w => wSigma L (w + -b)) z = (m2 : WithTop ℤ))
    (h3 : meromorphicOrderAt (fun w => wSigma L (w + -c)) z = (m3 : WithTop ℤ))
    (hN : ((k + (m1 + m2 + m3) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (nAux L b c) z) :
    (k : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by sorry
