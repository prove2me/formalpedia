-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermDenom_eventually_ne
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.threeTermDenom_eventually_ne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:48:02.630066+00:00
-- url     : https://prove2.me/theorems/bc9a2272-f760-4055-833c-949feefc73e7
-- title:
--   Three Term Relation: three Term Denom eventually ne
-- statement:
--   The Three Term Relation construction uses the three Term Denom eventually ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L119-L123

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.threeTermDenom_eventually_ne (he : SigmaEntire) (hord : SigmaOrder) (z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, threeTermDenom L b c x ≠ 0 := by sorry
