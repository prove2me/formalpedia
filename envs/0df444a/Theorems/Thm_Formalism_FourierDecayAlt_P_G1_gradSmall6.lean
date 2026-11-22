-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G1_gradSmall6
-- name    : Formalism.FourierDecayAlt.P.G1.gradSmall6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:33.827901+00:00
-- url     : https://prove2.me/theorems/aa80573f-5041-44e2-976d-762d761028d4
-- title:
--   G1: grad Small6
-- statement:
--   The G1 construction uses the grad Small6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L40-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L40-L129

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G1
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G1.gradSmall6 (m : ℕ) (D' : ℂ) (hD : D' ≠ 0) (x : Fin (m + 1) → ℂ) (hx : ∀ k, x k ≠ 0)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / (4 * ((m : ℝ) + 2))) (h : ∀ k, ‖dg0 D' x k‖ < η) :
    ∃ z : ℂ, z ^ (m + 2) = D' ∧ ∀ k, ‖x k - z‖ ≤ 6 * η * ‖z‖ := by sorry
