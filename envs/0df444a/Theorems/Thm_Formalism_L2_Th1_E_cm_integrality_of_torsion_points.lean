-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_cm_integrality_of_torsion_points
-- name    : Formalism.L2.Th1.E.cm_integrality_of_torsion_points
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:45:23.42736+00:00
-- url     : https://prove2.me/theorems/f34793e9-55ca-5132-b26e-3de3f75b4de0
-- title:
--   E: cm integrality of torsion points
-- statement:
--   The E construction uses the cm integrality of torsion points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L89-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L89-L116

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1

theorem Formalism.L2.Th1.E.cm_integrality_of_torsion_points (hP : PtOfInt) : CMIntegrality := by sorry
