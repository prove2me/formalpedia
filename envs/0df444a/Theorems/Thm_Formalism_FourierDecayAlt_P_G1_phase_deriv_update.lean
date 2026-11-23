-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G1_phase_deriv_update
-- name    : Formalism.FourierDecayAlt.P.G1.phase_deriv_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:06.777436+00:00
-- url     : https://prove2.me/theorems/11456075-1650-4965-9609-65c893facc5b
-- title:
--   G1: phase deriv update
-- statement:
--   The G1 construction uses the phase deriv update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L20-L24

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

theorem Formalism.FourierDecayAlt.P.G1.phase_deriv_update {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (j i : Fin n) (ξ : ℂ) :
    dg0 D' (Function.update x j ξ) i =
      1 - D' / (ξ * ∏ l ∈ univ \ {j}, x l) / (Function.update x j ξ i) := by sorry
