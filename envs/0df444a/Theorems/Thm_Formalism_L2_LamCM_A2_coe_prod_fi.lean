-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_coe_prod_fi
-- name    : Formalism.L2.LamCM.A2.coe_prod_fi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:46.183867+00:00
-- url     : https://prove2.me/theorems/a8a6feea-3235-48ee-9926-0910a9f3ddcd
-- title:
--   A2: coe prod fi
-- statement:
--   The A2 construction uses the coe prod fi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L309-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L309-L314

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
open scoped Pointwise

theorem Formalism.L2.LamCM.A2.coe_prod_fi {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ j ∈ s, I j : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ∏ j ∈ s, (I j : Submodule (𝓞 K) K) := by sorry
