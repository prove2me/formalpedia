-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_bcI_coeIdeal
-- name    : Formalism.L2.LamCM.bcI_coeIdeal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:52.314467+00:00
-- url     : https://prove2.me/theorems/b4647cd2-a26d-40fa-9517-2792fe56255d
-- title:
--   Lam CM: bc I coe Ideal
-- statement:
--   The Lam CM construction uses the bc I coe Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L140-L142

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

theorem Formalism.L2.LamCM.bcI_coeIdeal (J : Ideal (𝓞 K)) :
    bcI (K1 := K1) (J : FractionalIdeal (𝓞 K)⁰ K) = ((J.map (algebraMap (𝓞 K) (𝓞 K1)) : Ideal (𝓞 K1)) :
      FractionalIdeal (𝓞 K1)⁰ K1) := by sorry
