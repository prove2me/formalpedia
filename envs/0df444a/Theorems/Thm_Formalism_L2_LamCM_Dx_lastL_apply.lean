-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
-- name    : Formalism.L2.LamCM.Dx.lastL_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:49.194847+00:00
-- url     : https://prove2.me/theorems/493db49f-d045-487c-a20e-31fcce1de6e0
-- title:
--   Dx: last L apply
-- statement:
--   The Dx construction uses the last L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L76-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L76-L76

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
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
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.Dx.lastL_apply {n : ℕ} (v : Fin (n+1) → K) : lastL K n v = v (Fin.last n) := by sorry

attribute [defeq] Formalism.L2.LamCM.Dx.lastL_apply
