-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_prod_mul_le_detIdeal
-- name    : Formalism.L2.LamCM.A2.prod_mul_le_detIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:51.299541+00:00
-- url     : https://prove2.me/theorems/8cf1436d-94c4-401b-bcb3-ba40d965eaac
-- title:
--   A2: prod mul le det Ideal
-- statement:
--   The A2 construction uses the prod mul le det Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L316-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L316-L341

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

theorem Formalism.L2.LamCM.A2.prod_mul_le_detIdeal {m : ℕ} (L : MLat K m) (hL : L.Good) (ℓ : Fin m → MLine K)
    (u : Fin m → Fin m → K) (hu : ∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ L.M) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of u).det ≤ L.detIdeal := by sorry
