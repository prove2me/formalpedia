-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_mul_le_mul_r
-- name    : Formalism.L2.LamCM.mul_le_mul_r
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:33.298522+00:00
-- url     : https://prove2.me/theorems/5e5ebc3d-bb22-4d1c-a948-309f26de316c
-- title:
--   Lam CM: mul le mul r
-- statement:
--   The Lam CM construction uses the mul le mul r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L25-L27

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

theorem Formalism.L2.LamCM.mul_le_mul_r {A B : FractionalIdeal (𝓞 K)⁰ K} (h : A ≤ B) (C : FractionalIdeal (𝓞 K)⁰ K) :
    A * C ≤ B * C := by sorry
