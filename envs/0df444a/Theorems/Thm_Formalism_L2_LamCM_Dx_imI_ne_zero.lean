-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_imI_ne_zero
-- name    : Formalism.L2.LamCM.Dx.imI_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:48.721368+00:00
-- url     : https://prove2.me/theorems/f371748d-a08f-4e28-83ed-7f34bcd66a00
-- title:
--   Dx: im I ne zero
-- statement:
--   The Dx construction uses the im I ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L292-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L292-L298

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

theorem Formalism.L2.LamCM.Dx.imI_ne_zero {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : imI M hM ≠ 0 := by sorry
