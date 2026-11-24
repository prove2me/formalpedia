-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_le_one_mul
-- name    : Formalism.L2.LamCM.le_one_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:47.623981+00:00
-- url     : https://prove2.me/theorems/5ced19af-28af-48da-85ed-5de46f553c29
-- title:
--   Lam CM: le one mul
-- statement:
--   The Lam CM construction uses the le one mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L32-L36

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
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
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.le_one_mul {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≤ 1) (hB : B ≤ 1) : A * B ≤ 1 := by sorry
