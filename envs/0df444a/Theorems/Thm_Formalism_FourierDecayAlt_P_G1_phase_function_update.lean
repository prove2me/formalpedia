-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G1_phase_function_update
-- name    : Formalism.FourierDecayAlt.P.G1.phase_function_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:09.636629+00:00
-- url     : https://prove2.me/theorems/fa939fec-1870-4962-9fe3-524171d18c27
-- title:
--   G1: phase function update
-- statement:
--   The G1 construction uses the phase function update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L14-L18

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

theorem Formalism.FourierDecayAlt.P.G1.phase_function_update {n : ℕ} (D' : ℂ) (x : Fin n → ℂ) (k : Fin n) (ξ : ℂ) :
    g0 D' (Function.update x k ξ) =
      ξ + ∑ j ∈ univ \ {k}, x j + D' / (ξ * ∏ j ∈ univ \ {k}, x j) := by sorry
