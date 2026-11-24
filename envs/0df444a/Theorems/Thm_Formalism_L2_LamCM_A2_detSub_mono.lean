-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_detSub_mono
-- name    : Formalism.L2.LamCM.A2.detSub_mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:31.077181+00:00
-- url     : https://prove2.me/theorems/0eb284b8-d6a1-49f6-81fc-0e5d43f9536d
-- title:
--   A2: det Sub mono
-- statement:
--   The A2 construction uses the det Sub mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L139-L140

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

theorem Formalism.L2.LamCM.A2.detSub_mono {m : ℕ} {L L' : MLat K m} (h : L'.M ≤ L.M) : L'.detSub ≤ L.detSub := by sorry
