-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_sum_comp_algebraMap
-- name    : Formalism.L2.LamCM.sum_comp_algebraMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:23.605925+00:00
-- url     : https://prove2.me/theorems/63c7ab16-4b4c-49b7-b663-1460d4f6b6bd
-- title:
--   Lam CM: sum comp algebra Map
-- statement:
--   The Lam CM construction uses the sum comp algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L195-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L195-L214

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

theorem Formalism.L2.LamCM.sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ σ1 : K1 →+* ℂ, f (σ1.comp (algebraMap K K1)) = (Module.finrank K K1 : ℝ) * ∑ σ : K →+* ℂ, f σ := by sorry
