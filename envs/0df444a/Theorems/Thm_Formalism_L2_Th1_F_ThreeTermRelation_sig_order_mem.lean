-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_mem
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.sig_order_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:57.009458+00:00
-- url     : https://prove2.me/theorems/2a97d24f-6223-4a8b-acc6-9d11befce997
-- title:
--   Three Term Relation: sig order mem
-- statement:
--   The Three Term Relation construction uses the sig order mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L97-L102

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.sig_order_mem (hord : SigmaOrder) {β z : ℂ} (h : z + β ∈ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L (w + β)) z = ((1 : ℤ) : WithTop ℤ) := by sorry
