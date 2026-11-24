-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_det_eq
-- name    : Formalism.L2.Th1.F.ThreeTermRelation.det_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:00.245223+00:00
-- url     : https://prove2.me/theorems/913f9f5e-fa51-49b2-bfd6-cb0bf751cbe0
-- title:
--   Three Term Relation: det eq
-- statement:
--   The Three Term Relation construction uses the det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L326-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean#L326-L332

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

theorem Formalism.L2.Th1.F.ThreeTermRelation.det_eq (a : ℂ) :
    Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                  1, L.weierstrassP b, L.derivWeierstrassP b;
                  1, L.weierstrassP c, L.derivWeierstrassP c] = threeTermDet L b c a := by sorry
