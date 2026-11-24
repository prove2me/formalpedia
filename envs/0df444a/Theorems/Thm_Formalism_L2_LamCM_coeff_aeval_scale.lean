-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_coeff_aeval_scale
-- name    : Formalism.L2.LamCM.coeff_aeval_scale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:59.737948+00:00
-- url     : https://prove2.me/theorems/eef6d82b-a095-43ca-9708-0a6939448282
-- title:
--   Lam CM: coeff aeval scale
-- statement:
--   The Lam CM construction uses the coeff aeval scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsEvalNeZeroOfTotalDegreeLt.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsEvalNeZeroOfTotalDegreeLt.lean#L42-L57

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
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
open MvPolynomial IsLocalRing

theorem Formalism.L2.LamCM.coeff_aeval_scale {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    coeff μ (aeval (fun w => C (c w) * X w) F) = coeff μ F * ∏ w, c w ^ μ w := by sorry
