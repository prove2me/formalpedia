-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_prod_bound
-- name    : Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_prod_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:10.042864+00:00
-- url     : https://prove2.me/theorems/7a28214f-727b-458b-af2a-bf73f8d790c6
-- title:
--   Phase Function Derivatives: a prod bound
-- statement:
--   The Phase Function Derivatives construction uses the a prod bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L90-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L90-L118

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_prod_bound {n : ℕ} (N : ℕ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) (b : ℝ)
    (hb : ∀ k, ‖x k‖⁻¹ ≤ b) :
    ‖iteratedFDeriv ℂ N (fun y : Fin n → ℂ => ∏ k, (y k)⁻¹) x‖ ≤
      a_cst n N * ((∏ k, ‖x k‖⁻¹) * b ^ N) := by sorry
