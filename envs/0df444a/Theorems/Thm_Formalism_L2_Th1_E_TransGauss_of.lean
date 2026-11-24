-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_TransGauss_of
-- name    : Formalism.L2.Th1.E.TransGauss_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:44.18119+00:00
-- url     : https://prove2.me/theorems/0cd52947-a8ac-449a-9566-c0bce105c489
-- title:
--   E: Trans Gauss of
-- statement:
--   The E construction uses the Trans Gauss of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L148-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ScaledXOffOrigin.lean#L148-L158

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXOffOrigin
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
open Main
set_option linter.unusedVariables false

theorem Formalism.L2.Th1.E.TransGauss_of (hR : IntRules) (hA : UnitAtRules) (hU : TransUnit) : TransGauss := by sorry
