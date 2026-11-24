-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
-- name    : Formalism.L2.LamCM.Dx.snocL_castSucc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:40.346828+00:00
-- url     : https://prove2.me/theorems/50f27d9a-bf5c-4be8-96f8-4ea13ad70a39
-- title:
--   Dx: snoc L cast Succ
-- statement:
--   The Dx construction uses the snoc L cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L70-L71

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

theorem Formalism.L2.LamCM.Dx.snocL_castSucc {n : ℕ} (w : Fin n → K) (j : Fin n) : snocL K n w (Fin.castSucc j) = w j := by sorry
