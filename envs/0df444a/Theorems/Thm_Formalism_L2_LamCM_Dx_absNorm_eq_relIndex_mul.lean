-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_Dx_absNorm_eq_relIndex_mul
-- name    : Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:25.298882+00:00
-- url     : https://prove2.me/theorems/8c4183ca-e37b-467f-b2b9-3c1d4ac56f46
-- title:
--   Dx: abs Norm eq rel Index mul
-- statement:
--   The Dx construction uses the abs Norm eq rel Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L176-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean#L176-L229

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

theorem Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul (J J' : FractionalIdeal (𝓞 K)⁰ K) (hJ' : J' ≠ 0) (hle : J' ≤ J) :
    FractionalIdeal.absNorm J' = ((J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (J : Submodule (𝓞 K) K).toAddSubgroup : ℚ) * FractionalIdeal.absNorm J := by sorry
