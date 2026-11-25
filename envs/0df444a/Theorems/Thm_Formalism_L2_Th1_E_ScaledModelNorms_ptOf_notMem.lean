-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_ptOf_notMem
-- name    : Formalism.L2.Th1.E.ScaledModelNorms.ptOf_notMem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:29.738165+00:00
-- url     : https://prove2.me/theorems/1c61a6b6-9404-4428-82c5-1ba7211f0092
-- title:
--   Scaled Model Norms: pt Of not Mem
-- statement:
--   The Scaled Model Norms construction uses the pt Of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L70-L73

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
variable (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem Formalism.L2.Th1.E.ScaledModelNorms.ptOf_notMem (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (nonsing l L ι hΔ t ht) := by sorry
