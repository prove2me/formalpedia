-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Homog_wSigma_scale
-- name    : Formalism.L2.Th1.F.Homog.wSigma_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:32.806836+00:00
-- url     : https://prove2.me/theorems/bb7870b9-7e8e-4cf7-9fe6-d1eba8915a46
-- title:
--   Homog: w Sigma scale
-- statement:
--   The Homog construction uses the w Sigma scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L185-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L185-L190

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
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
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)

theorem Formalism.L2.Th1.F.Homog.wSigma_scale (z : ℂ) : wSigma (scalePair L c hc) (c * z) = c * wSigma L z := by sorry
