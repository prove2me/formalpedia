-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_intCurve_short
-- name    : Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:40:57.495066+00:00
-- url     : https://prove2.me/theorems/f70925cd-1079-5d07-bb3b-beaf1b384c6b
-- title:
--   Scaled Model Norms: int Curve short
-- statement:
--   The Scaled Model Norms construction uses the int Curve short property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L41-L55

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
variable (l : ℕ) [Fact l.Prime]

theorem Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short (hl : 5 ≤ l) (g2 g3 : ℂ_[l]) (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1)
    (hD : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) : IntCurve (A.shortW g2 g3) := by sorry
