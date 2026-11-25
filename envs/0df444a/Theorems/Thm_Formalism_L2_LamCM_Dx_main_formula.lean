-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_main_formula
-- name    : Formalism.L2.LamCM.Dx.main_formula
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:25.362814+00:00
-- url     : https://prove2.me/theorems/6111b5c7-cf0b-5e02-ae03-26aa2d20e6e6
-- title:
--   Dx: main formula
-- statement:
--   The Dx construction uses the main formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L367-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L367-L384

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

theorem Formalism.L2.LamCM.Dx.main_formula : ∀ (n : ℕ) (M' M : Submodule (𝓞 K) (Fin n → K)), M' ≤ M → Sand M' → Sand M →
    FractionalIdeal.absNorm (fiD M') = (M'.toAddSubgroup.relIndex M.toAddSubgroup : ℚ) * FractionalIdeal.absNorm (fiD M) := by sorry
