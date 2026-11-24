-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Cm1_conj_theta
-- name    : Formalism.L2.Th1.F.Cm1.conj_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:19.894933+00:00
-- url     : https://prove2.me/theorems/176b335f-088a-458d-8d01-ee6bbcd0a638
-- title:
--   Cm1: conj theta
-- statement:
--   The Cm1 construction uses the conj theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/CmAlternatingForm.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/CmAlternatingForm.lean#L33-L38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Cm1

theorem Formalism.L2.Th1.F.Cm1.conj_theta (b : ℤ) (d : ℕ) :
    conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by sorry
