-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_idx
-- name    : Formalism.L2.LamCM.Dx.idx
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:30.601038+00:00
-- url     : https://prove2.me/theorems/bcf0b1f6-2d64-477a-af81-2b1253e42eb7
-- title:
--   Dx: idx
-- statement:
--   The Dx construction uses the idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L146-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L146-L174

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

theorem Formalism.L2.LamCM.Dx.idx {G H : Type*} [AddCommGroup G] [AddCommGroup H] (A' A : AddSubgroup G) (hA : A' ≤ A) (f : G →+ H) :
    A'.relIndex A = (A' ⊓ f.ker).relIndex (A ⊓ f.ker) * (A'.map f).relIndex (A.map f) := by sorry
