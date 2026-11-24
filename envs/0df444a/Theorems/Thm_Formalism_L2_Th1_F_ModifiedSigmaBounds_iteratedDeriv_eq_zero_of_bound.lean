-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_iteratedDeriv_eq_zero_of_bound
-- name    : Formalism.L2.Th1.F.ModifiedSigmaBounds.iteratedDeriv_eq_zero_of_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:08.397876+00:00
-- url     : https://prove2.me/theorems/fc2d2f0d-7ec2-4333-b443-6ba0080ec364
-- title:
--   Modified Sigma Bounds: iterated Deriv eq zero of bound
-- statement:
--   The Modified Sigma Bounds construction uses the iterated Deriv eq zero of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L142-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SgStar.lean#L142-L164

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
open Formalism.L2.Th1.F.ModifiedSigmaBounds
open SigmaConv

theorem Formalism.L2.Th1.F.ModifiedSigmaBounds.iteratedDeriv_eq_zero_of_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K r : ℝ} (hr : 0 < r)
    (hb : ∀ z, ‖z‖ < r → ‖f z‖ ≤ K * ‖z‖ ^ 4) (n : ℕ) (hn : n < 4) : iteratedDeriv n f 0 = 0 := by sorry
