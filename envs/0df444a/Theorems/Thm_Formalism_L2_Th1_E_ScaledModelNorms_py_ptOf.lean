-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_ScaledModelNorms_py_ptOf
-- name    : Formalism.L2.Th1.E.ScaledModelNorms.py_ptOf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:22.587594+00:00
-- url     : https://prove2.me/theorems/abd4c238-e969-52e6-b969-515d2d62495f
-- title:
--   Scaled Model Norms: py pt Of
-- statement:
--   The Scaled Model Norms construction uses the py pt Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/CmIntegralityOfTorsionPoints.lean#L80-L83

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

theorem Formalism.L2.Th1.E.ScaledModelNorms.py_ptOf (hΔ : (curveL l L ι).Δ ≠ 0) (t : ℂ) (ht : t ∉ L.lattice) :
    py (curveL l L ι) (ptOf l L ι t) = ι (L.derivWeierstrassP t) / 2 := by sorry
