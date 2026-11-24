-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_abs_norm_eq_prod
-- name    : Formalism.L2.LamCM.A2.abs_norm_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:51.749231+00:00
-- url     : https://prove2.me/theorems/dea9b584-25be-4e79-a07d-bd7c94f25d4e
-- title:
--   A2: abs norm eq prod
-- statement:
--   The A2 construction uses the abs norm eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L43-L47

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

theorem Formalism.L2.LamCM.A2.abs_norm_eq_prod (x : K) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by sorry
