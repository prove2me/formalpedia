-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_halfShift_of
-- name    : Formalism.L2.Th1.F.halfShift_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:37.746482+00:00
-- url     : https://prove2.me/theorems/0e337145-0bfb-4290-8892-c7009299ef8b
-- title:
--   F: half Shift of
-- statement:
--   The F construction uses the half Shift of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassPSecondDerivative.lean#L153-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassPSecondDerivative.lean#L153-L203

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open HalfPeriodDerivative

theorem Formalism.L2.Th1.F.halfShift_of (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (hi : PInjective) :
    HalfShift := by sorry
