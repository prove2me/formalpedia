-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_eventually_notMem
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.eventually_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:41.315422+00:00
-- url     : https://prove2.me/theorems/8c4d5638-97f3-482c-bcf6-b51e83425bd0
-- title:
--   Three Term Relation: eventually not Mem
-- statement:
--   The Three Term Relation construction uses the eventually not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L28-L32

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.eventually_notMem (L : PeriodPair) (z : ℂ) : ∀ᶠ x in 𝓝[≠] z, x ∉ L.lattice := by sorry
