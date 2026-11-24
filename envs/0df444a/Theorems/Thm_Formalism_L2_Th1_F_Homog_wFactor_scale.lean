-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_Homog_wFactor_scale
-- name    : Formalism.L2.Th1.F.Homog.wFactor_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:32.369102+00:00
-- url     : https://prove2.me/theorems/763230cb-6067-41f2-beda-04b89e30d5ba
-- title:
--   Homog: w Factor scale
-- statement:
--   The Homog construction uses the w Factor scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/LatticeOnly.lean#L177-L183

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
omit L
include hc

theorem Formalism.L2.Th1.F.Homog.wFactor_scale (l z : ℂ) : wFactor (c * l) (c * z) = wFactor l z := by sorry
