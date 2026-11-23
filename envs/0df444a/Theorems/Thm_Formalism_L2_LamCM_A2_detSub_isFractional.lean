-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_detSub_isFractional
-- name    : Formalism.L2.LamCM.A2.detSub_isFractional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:04.438952+00:00
-- url     : https://prove2.me/theorems/0f3ce4aa-3d5e-4851-887b-e1aa6103bc90
-- title:
--   A2: det Sub is Fractional
-- statement:
--   The A2 construction uses the det Sub is Fractional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L77-L91

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
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
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.A2.detSub_isFractional {m : ℕ} (L : MLat K m) (hM : L.M.FG) : IsFractional (𝓞 K)⁰ L.detSub := by sorry
