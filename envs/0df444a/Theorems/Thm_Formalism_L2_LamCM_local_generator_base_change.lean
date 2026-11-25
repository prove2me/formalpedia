-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_local_generator_base_change
-- name    : Formalism.L2.LamCM.local_generator_base_change
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:53.983698+00:00
-- url     : https://prove2.me/theorems/ade21a97-ef70-43eb-b237-d3a4237850f1
-- title:
--   Lam CM: local generator base change
-- statement:
--   The Lam CM construction uses the local generator base change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L239-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L239-L258

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero
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

theorem Formalism.L2.LamCM.local_generator_base_change : LocGenBaseChange := by sorry
