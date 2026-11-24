-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_count_coeIdeal_eq_zero
-- name    : Formalism.L2.LamCM.count_coeIdeal_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:14.877801+00:00
-- url     : https://prove2.me/theorems/dc71dea1-e311-4923-ad82-faaa13c3786e
-- title:
--   Lam CM: count coe Ideal eq zero
-- statement:
--   The Lam CM construction uses the count coe Ideal eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L23-L24

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
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.L2.LamCM.count_coeIdeal_eq_zero (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (h : ¬ J ≤ v.asIdeal) :
    FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0 := by sorry
