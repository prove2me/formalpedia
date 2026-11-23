-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_b_near
-- name    : Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.b_near
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:32.832718+00:00
-- url     : https://prove2.me/theorems/51b25cec-fb2c-4630-8bfb-85938b58f3b0
-- title:
--   Phase Function Derivatives: b near
-- statement:
--   The Phase Function Derivatives construction uses the b near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L270-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L270-L334

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

theorem Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.b_near (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 100 * ((m : ℝ) + 2) * δ ≤ ‖z‖)
    (x : Fin (m + 1) → ℂ) (hx : ∀ k, ‖x k - z‖ ≤ 2 * δ) (hx0 : ∀ k, x k ≠ 0) (k : Fin (m + 1)) :
    ‖x k - z‖ ≤ 6 * ‖z‖ * ‖dg0 (z ^ (m + 2)) x‖ := by sorry
