-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_norm_nat
-- name    : Formalism.L2.Th1.E.ScaledModelNorms.norm_nat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:28:37.406429+00:00
-- url     : https://prove2.me/theorems/ad82a442-738f-5edf-a16e-73b385749a67
-- title:
--   Scaled Model Norms: norm nat
-- statement:
--   The Scaled Model Norms construction uses the norm nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L26-L31

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

theorem Formalism.L2.Th1.E.ScaledModelNorms.norm_nat {N : ℕ} (h : ¬ l ∣ N) : ‖(N : ℂ_[l])‖ = 1 := by sorry
