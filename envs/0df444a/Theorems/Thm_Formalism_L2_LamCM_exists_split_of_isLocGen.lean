-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_exists_split_of_isLocGen
-- name    : Formalism.L2.LamCM.exists_split_of_isLocGen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:19.583595+00:00
-- url     : https://prove2.me/theorems/5235eb6f-43c7-485e-aa99-5eb0537bf958
-- title:
--   Lam CM: exists split of is Loc Gen
-- statement:
--   The Lam CM construction uses the exists split of is Loc Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L34-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L34-L88

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

theorem Formalism.L2.LamCM.exists_split_of_isLocGen (v : HeightOneSpectrum (𝓞 F)) {c : F} {I : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0)
    (hc : IsLocGen v c I) :
    ∃ A B : Ideal (𝓞 F), ¬ A ≤ v.asIdeal ∧ ¬ B ≤ v.asIdeal ∧
      I * (B : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ c * (A : FractionalIdeal (𝓞 F)⁰ F) := by sorry
