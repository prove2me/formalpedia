-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_bcI_spanSingleton
-- name    : Formalism.L2.LamCM.bcI_spanSingleton
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:06.958708+00:00
-- url     : https://prove2.me/theorems/36b60572-cbb4-4efb-90b3-c741c4be4553
-- title:
--   Lam CM: bc I span Singleton
-- statement:
--   The Lam CM construction uses the bc I span Singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L135-L138

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

theorem Formalism.L2.LamCM.bcI_spanSingleton (x : K) :
    bcI (K1 := K1) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 K1)⁰ (algebraMap K K1 x) := by sorry
