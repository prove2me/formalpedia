-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_parallelogram_sum_two
-- name    : Formalism.L2.Th1.E.parallelogram_sum_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:50.296604+00:00
-- url     : https://prove2.me/theorems/99471bde-58ef-47f1-953f-d8450e457d24
-- title:
--   E: parallelogram sum two
-- statement:
--   The E construction uses the parallelogram sum two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L138-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXEqOffOrigin.lean#L138-L160

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E

theorem Formalism.L2.Th1.E.parallelogram_sum_two : ParSumTwo := by sorry
