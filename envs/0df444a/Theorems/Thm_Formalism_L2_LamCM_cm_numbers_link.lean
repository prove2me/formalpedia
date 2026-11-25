-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_cm_numbers_link
-- name    : Formalism.L2.LamCM.cm_numbers_link
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:20.238899+00:00
-- url     : https://prove2.me/theorems/91ec0eb6-49a4-40b5-b482-2d8494abb744
-- title:
--   Lam CM: cm numbers link
-- statement:
--   The Lam CM construction uses the cm numbers link property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CmNumbersLink.lean#L8-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CmNumbersLink.lean#L8-L8

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.LamCM

theorem Formalism.L2.LamCM.cm_numbers_link : CMNumbersLink := by sorry
