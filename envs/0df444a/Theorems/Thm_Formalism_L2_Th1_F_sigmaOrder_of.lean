-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_sigmaOrder_of
-- name    : Formalism.L2.Th1.F.sigmaOrder_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:09.659751+00:00
-- url     : https://prove2.me/theorems/d0ef51a9-68a5-40b1-ac37-eb977a6ab280
-- title:
--   F: sigma Order of
-- statement:
--   The F construction uses the sigma Order of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaOrder.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaOrder.lean#L7-L37

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F

theorem Formalism.L2.Th1.F.sigmaOrder_of (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by sorry
