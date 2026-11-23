-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_b_differentiableAt
-- name    : Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.b_differentiableAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:40.060654+00:00
-- url     : https://prove2.me/theorems/c1a6875f-ef8b-401a-a0e6-f1e7f73accbb
-- title:
--   Phase Function Derivatives: b differentiable At
-- statement:
--   The Phase Function Derivatives construction uses the b differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L264-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L264-L268

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

theorem Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.b_differentiableAt {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) :
    DifferentiableAt ℂ (g0 D') x := by sorry
