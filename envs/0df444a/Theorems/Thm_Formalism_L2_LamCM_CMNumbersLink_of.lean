-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_CMNumbersLink_of
-- name    : Formalism.L2.LamCM.CMNumbersLink_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:11.960743+00:00
-- url     : https://prove2.me/theorems/76ca430c-e3d0-485d-ad14-1996a0403eb7
-- title:
--   Lam CM: CMNumbers Link of
-- statement:
--   The Lam CM construction uses the CMNumbers Link of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L202-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L202-L208

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem Formalism.L2.LamCM.CMNumbersLink_of (hH : HadamardIdeals) (hD : DetGood) : CMNumbersLink := by sorry
