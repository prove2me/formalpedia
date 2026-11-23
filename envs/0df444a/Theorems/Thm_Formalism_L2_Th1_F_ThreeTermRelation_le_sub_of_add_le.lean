-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_le_sub_of_add_le
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.le_sub_of_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:06.750134+00:00
-- url     : https://prove2.me/theorems/aec7d8b6-f1bd-4ecc-9ef4-b57fc0562ac8
-- title:
--   Three Term Relation: le sub of add le
-- statement:
--   The Three Term Relation construction uses the le sub of add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L10-L17

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.le_sub_of_add_le {o : WithTop ℤ} {m k : ℤ} (h : ((k + m : ℤ) : WithTop ℤ) ≤ o) :
    (k : WithTop ℤ) ≤ o - (m : WithTop ℤ) := by sorry
