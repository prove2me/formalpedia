-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_det_mem
-- name    : Formalism.L2.LamCM.A2.det_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:11.10881+00:00
-- url     : https://prove2.me/theorems/fad9758e-3cc4-48b5-b0c2-19e31317a3fa
-- title:
--   A2: det mem
-- statement:
--   The A2 construction uses the det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L99-L101

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

theorem Formalism.L2.LamCM.A2.det_mem {m : ℕ} (L : MLat K m) (x : Fin m → Fin m → K) (hx : ∀ i, x i ∈ L.M) :
    (Matrix.of x).det ∈ L.detSub := by sorry
