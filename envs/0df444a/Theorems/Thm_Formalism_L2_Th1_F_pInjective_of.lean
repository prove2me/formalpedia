-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_pInjective_of
-- name    : Formalism.L2.Th1.F.pInjective_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:41.840975+00:00
-- url     : https://prove2.me/theorems/8411a738-20c9-4124-a105-5ee9a9df8d07
-- title:
--   F: p Injective of
-- statement:
--   The F construction uses the p Injective of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L259-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean#L259-L280

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F

theorem Formalism.L2.Th1.F.pInjective_of (h : SigmaAdd) (hz : SigmaZero) : PInjective := by sorry
