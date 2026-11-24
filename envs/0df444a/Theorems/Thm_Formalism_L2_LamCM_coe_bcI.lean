-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_coe_bcI
-- name    : Formalism.L2.LamCM.coe_bcI
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:14.718893+00:00
-- url     : https://prove2.me/theorems/a9607edb-27f3-4cdb-a341-af1ef4abd381
-- title:
--   Lam CM: coe bc I
-- statement:
--   The Lam CM construction uses the coe bc I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L120-L124

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

theorem Formalism.L2.LamCM.coe_bcI (I : FractionalIdeal (𝓞 K)⁰ K) :
    ((bcI (K1 := K1) I : FractionalIdeal (𝓞 K1)⁰ K1) : Submodule (𝓞 K1) K1) =
      Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ I}) := by sorry
