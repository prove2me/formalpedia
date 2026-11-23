-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_coe
-- name    : Formalism.L2.LamCM.A2.detIdeal_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:06.92089+00:00
-- url     : https://prove2.me/theorems/48ccc5d8-df7f-47ec-ad68-2b13fcda8d18
-- title:
--   A2: det Ideal coe
-- statement:
--   The A2 construction uses the det Ideal coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L93-L97

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

theorem Formalism.L2.LamCM.A2.detIdeal_coe {m : ℕ} (L : MLat K m) (h : IsFractional (𝓞 K)⁰ L.detSub) :
    (L.detIdeal : Submodule (𝓞 K) K) = L.detSub := by sorry
