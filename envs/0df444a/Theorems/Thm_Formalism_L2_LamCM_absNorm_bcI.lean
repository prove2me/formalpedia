-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_absNorm_bcI
-- name    : Formalism.L2.LamCM.absNorm_bcI
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:19.742845+00:00
-- url     : https://prove2.me/theorems/9941002b-37e7-464e-b838-eeed486a88ab
-- title:
--   Lam CM: abs Norm bc I
-- statement:
--   The Lam CM construction uses the abs Norm bc I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L160-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L160-L183

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
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]

theorem Formalism.L2.LamCM.absNorm_bcI (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (bcI (K1 := K1) I) = (FractionalIdeal.absNorm I) ^ Module.finrank K K1 := by sorry
