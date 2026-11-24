-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_norm_algebraMap_tower
-- name    : Formalism.L2.LamCM.norm_algebraMap_tower
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:14.149996+00:00
-- url     : https://prove2.me/theorems/89a985fe-08e2-403c-a28b-e6d8cca91ab2
-- title:
--   Lam CM: norm algebra Map tower
-- statement:
--   The Lam CM construction uses the norm algebra Map tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/CountSpanSingletonAlgebraMapEqZero.lean#L156-L158

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

theorem Formalism.L2.LamCM.norm_algebraMap_tower (x : K) :
    Algebra.norm ℚ (algebraMap K K1 x) = (Algebra.norm ℚ x) ^ Module.finrank K K1 := by sorry
