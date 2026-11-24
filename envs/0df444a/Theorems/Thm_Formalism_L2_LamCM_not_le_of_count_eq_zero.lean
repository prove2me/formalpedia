-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_not_le_of_count_eq_zero
-- name    : Formalism.L2.LamCM.not_le_of_count_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:49.137275+00:00
-- url     : https://prove2.me/theorems/52de3af1-7f7a-4b2f-942c-6b65188ecf2c
-- title:
--   Lam CM: not le of count eq zero
-- statement:
--   The Lam CM construction uses the not le of count eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L26-L32

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

theorem Formalism.L2.LamCM.not_le_of_count_eq_zero (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥)
    (h : FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) = 0) : ¬ J ≤ v.asIdeal := by sorry
