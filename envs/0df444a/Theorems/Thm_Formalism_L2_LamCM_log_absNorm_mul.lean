-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_log_absNorm_mul
-- name    : Formalism.L2.LamCM.log_absNorm_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:01.614038+00:00
-- url     : https://prove2.me/theorems/9cb2a1cd-9677-4309-b382-571156aa9b0e
-- title:
--   Lam CM: log abs Norm mul
-- statement:
--   The Lam CM construction uses the log abs Norm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L20-L23

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

theorem Formalism.L2.LamCM.log_absNorm_mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Real.log ((FractionalIdeal.absNorm (I * J) : ℚ) : ℝ) =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) + Real.log ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by sorry
