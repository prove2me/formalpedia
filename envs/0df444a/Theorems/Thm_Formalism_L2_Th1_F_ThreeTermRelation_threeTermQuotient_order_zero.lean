-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_zero
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:42.150709+00:00
-- url     : https://prove2.me/theorems/fb8d182b-7e9c-4f21-96c5-64a00043c346
-- title:
--   Three Term Relation: three Term Quotient order zero
-- statement:
--   The Three Term Relation construction uses the three Term Quotient order zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L234-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L234-L246

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_zero (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    0 ≤ meromorphicOrderAt (threeTermQuotient L b c) 0 := by sorry
