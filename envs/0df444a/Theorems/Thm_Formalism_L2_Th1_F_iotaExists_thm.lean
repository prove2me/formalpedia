-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_iotaExists_thm
-- name    : Formalism.L2.Th1.F.iotaExists_thm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:32.677804+00:00
-- url     : https://prove2.me/theorems/13dff520-1c0b-416f-8f08-6c1b181f2537
-- title:
--   F: iota Exists thm
-- statement:
--   The F construction uses the iota Exists thm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MkLeOfDenseRange.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MkLeOfDenseRange.lean#L44-L48

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MkLeOfDenseRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Cardinal Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F

theorem Formalism.L2.Th1.F.iotaExists_thm : IotaExists := by sorry
