-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_CmBy_ne_zero
-- name    : Formalism.L2.Th1.F.CmBy.ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:20:21.472165+00:00
-- url     : https://prove2.me/theorems/b23ecb4b-8c5e-4d10-837d-50037a4b03a2
-- title:
--   Cm By: ne zero
-- statement:
--   The Cm By construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HasCMByIsogenyOf.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HasCMByIsogenyOf.lean#L29-L45

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
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
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.CmBy

theorem Formalism.L2.Th1.F.CmBy.ne_zero (d : ℕ) (hd : 0 < d) (m n : ℤ) (h : (m, n) ≠ (0, 0)) :
    (m : ℂ) + (n : ℂ) * omegaK d ≠ 0 := by sorry
