-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_card_fibre
-- name    : Formalism.L2.LamCM.card_fibre
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:28.335668+00:00
-- url     : https://prove2.me/theorems/72b3016e-4393-49b8-9200-8c952e9a077e
-- title:
--   Lam CM: card fibre
-- statement:
--   The Lam CM construction uses the card fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L185-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L185-L193

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

theorem Formalism.L2.LamCM.card_fibre (σ : K →+* ℂ) :
    Nat.card {σ1 : K1 →+* ℂ // σ1.comp (algebraMap K K1) = σ} = Module.finrank K K1 := by sorry
