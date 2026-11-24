-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_th0Class_of
-- name    : Formalism.L2.Th1.F.th0Class_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:39.053734+00:00
-- url     : https://prove2.me/theorems/a7ab0f0b-eb83-43c5-9ad0-2012ded6189a
-- title:
--   F: th0 Class of
-- statement:
--   The F construction uses the th0 Class of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HermHalfRight.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/HermHalfRight.lean#L69-L81

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HermHalfRight
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
open ThetaZeroHermitianLemmas

theorem Formalism.L2.Th1.F.th0Class_of (hb : SgStarBasic) (hq : SgStarQuasi) : ThetaZeroClass := by sorry
