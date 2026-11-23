-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_ne_zero
-- name    : Formalism.L2.LamCM.A2.detIdeal_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:46.55478+00:00
-- url     : https://prove2.me/theorems/93040544-c47e-4e49-ae68-bb9d27d0b6fd
-- title:
--   A2: det Ideal ne zero
-- statement:
--   The A2 construction uses the det Ideal ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L115-L122

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

theorem Formalism.L2.LamCM.A2.detIdeal_ne_zero {m : ℕ} (L : MLat K m) (hL : L.Good) : L.detIdeal ≠ 0 := by sorry
