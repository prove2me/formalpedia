-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_hkLimit_of
-- name    : Formalism.L2.Th1.F.hkLimit_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:30:05.511522+00:00
-- url     : https://prove2.me/theorems/904d7719-cbb4-43a1-87b9-a32275024e4e
-- title:
--   F: hk Limit of
-- statement:
--   The F construction uses the hk Limit of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EisensteinS2LimitFormulaOfHkLimit.lean#L64-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EisensteinS2LimitFormulaOfHkLimit.lean#L64-L98

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EisensteinS2LimitFormulaOfHkLimit
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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Hk4

theorem Formalism.L2.Th1.F.hkLimit_of (h1 : HkSummable) (h2 : HkRowIntegral) (h3 : HkCellBound) (h4 : HkCellCont)
    (h5 : HkIntZero) (h6 : HkRowZero) (h7 : HkIntLimit) : HkLimit := by sorry
