-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_hadamardInequality
-- name    : Formalism.L2.LamCM.hadamardInequality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:18.461882+00:00
-- url     : https://prove2.me/theorems/da1e5102-ef10-4f2b-ab41-6f5d32fadfff
-- title:
--   Lam CM: hadamard Inequality
-- statement:
--   The Lam CM construction uses the hadamard Inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L234-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L234-L303

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

theorem Formalism.L2.LamCM.hadamardInequality : HadamardPD := by sorry
