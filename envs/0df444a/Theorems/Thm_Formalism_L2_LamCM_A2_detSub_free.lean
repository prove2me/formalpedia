-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_detSub_free
-- name    : Formalism.L2.LamCM.A2.detSub_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:13.072406+00:00
-- url     : https://prove2.me/theorems/2c537683-a205-4cc2-80f0-6e6198664a5f
-- title:
--   A2: det Sub free
-- statement:
--   The A2 construction uses the det Sub free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L163-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L163-L186

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

theorem Formalism.L2.LamCM.A2.detSub_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detSub = Submodule.span (𝓞 K) {(Matrix.of b).det} := by sorry
