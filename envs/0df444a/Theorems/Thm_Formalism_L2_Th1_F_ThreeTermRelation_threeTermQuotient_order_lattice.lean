-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_lattice
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_lattice
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:11.094846+00:00
-- url     : https://prove2.me/theorems/e7149701-f15a-4ea6-9087-a559c5a17869
-- title:
--   Three Term Relation: three Term Quotient order lattice
-- statement:
--   The Three Term Relation construction uses the three Term Quotient order lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L248-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L248-L256

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_lattice (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder) (hq : SigmaQuasi)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) {z : ℂ}
    (hzL : z ∈ L.lattice) : 0 ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by sorry
