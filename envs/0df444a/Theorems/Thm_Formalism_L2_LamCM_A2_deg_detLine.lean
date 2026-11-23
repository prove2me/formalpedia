-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_deg_detLine
-- name    : Formalism.L2.LamCM.A2.deg_detLine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:40.261878+00:00
-- url     : https://prove2.me/theorems/79ae814d-4b9e-41e9-82f9-dea84fa30e81
-- title:
--   A2: deg det Line
-- statement:
--   The A2 construction uses the deg det Line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L124-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L124-L125

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

theorem Formalism.L2.LamCM.A2.deg_detLine {m : ℕ} (L : MLat K m) : L.detLine.deg =
    -Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) - ∑ σ, Real.log (Real.sqrt (L.H σ).det.re) := by sorry
