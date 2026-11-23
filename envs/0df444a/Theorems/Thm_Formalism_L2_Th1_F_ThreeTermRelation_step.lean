-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_step
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:10.112404+00:00
-- url     : https://prove2.me/theorems/8eae4ced-0db0-4fa8-b897-a57e9da06df4
-- title:
--   Three Term Relation: step
-- statement:
--   The Three Term Relation construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L317-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L317-L324

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.step (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by sorry
