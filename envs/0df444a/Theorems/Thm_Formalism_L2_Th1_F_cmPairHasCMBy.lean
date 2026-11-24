-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_cmPairHasCMBy
-- name    : Formalism.L2.Th1.F.cmPairHasCMBy
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:38:57.059251+00:00
-- url     : https://prove2.me/theorems/0bb4fb33-ae61-4a27-b3c4-3772db467664
-- title:
--   F: cm Pair Has CMBy
-- statement:
--   The F construction uses the cm Pair Has CMBy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/HasCMByStable.lean#L9-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/HasCMByStable.lean#L9-L9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F

theorem Formalism.L2.Th1.F.cmPairHasCMBy : CmPairHasCMBy := by sorry
