-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_hadamardIdeals
-- name    : Formalism.L2.LamCM.hadamardIdeals
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:23.958028+00:00
-- url     : https://prove2.me/theorems/5eeda5ab-c437-4c9a-a66c-8b9f4a0f1e3d
-- title:
--   Lam CM: hadamard Ideals
-- statement:
--   The Lam CM construction uses the hadamard Ideals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L346-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L346-L419

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
open A2

theorem Formalism.L2.LamCM.hadamardIdeals : HadamardIdeals := by sorry
