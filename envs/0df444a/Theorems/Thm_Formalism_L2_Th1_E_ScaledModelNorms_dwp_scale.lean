-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_dwp_scale
-- name    : Formalism.L2.Th1.E.ScaledModelNorms.dwp_scale
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:22.494243+00:00
-- url     : https://prove2.me/theorems/9605c0e2-e114-5399-8a4b-7434d6fdb860
-- title:
--   Scaled Model Norms: dwp scale
-- statement:
--   The Scaled Model Norms construction uses the dwp scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L13-L22

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
open Formalism.L2.Th1.E.ScaledModelNorms
open Formalism.L2.Th1

theorem Formalism.L2.Th1.E.ScaledModelNorms.dwp_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (F.scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by sorry
