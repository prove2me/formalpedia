-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_free
-- name    : Formalism.L2.LamCM.A2.detIdeal_free
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:50.623516+00:00
-- url     : https://prove2.me/theorems/0451989e-5a3e-4d19-b4fd-b9a7aab5bdd1
-- title:
--   A2: det Ideal free
-- statement:
--   The A2 construction uses the det Ideal free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L188-L193

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

theorem Formalism.L2.LamCM.A2.detIdeal_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K) (hL : L.Good)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detIdeal = FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det := by sorry
