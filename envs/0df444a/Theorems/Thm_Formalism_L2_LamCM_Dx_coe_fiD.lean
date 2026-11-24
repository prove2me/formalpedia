-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_coe_fiD
-- name    : Formalism.L2.LamCM.Dx.coe_fiD
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:52.891972+00:00
-- url     : https://prove2.me/theorems/5a67d623-bf55-45ad-ae90-93d1aacdfc9c
-- title:
--   Dx: coe fi D
-- statement:
--   The Dx construction uses the coe fi D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L254-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L254-L255

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

theorem Formalism.L2.LamCM.Dx.coe_fiD {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (hM : Sand M) : (fiD M : Submodule (𝓞 K) K) = dS M := by sorry
