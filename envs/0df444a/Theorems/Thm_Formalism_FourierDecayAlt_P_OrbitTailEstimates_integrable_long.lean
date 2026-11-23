-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_integrable_long
-- name    : Formalism.FourierDecayAlt.P.OrbitTailEstimates.integrable_long
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:53.41714+00:00
-- url     : https://prove2.me/theorems/71f30bd8-386f-4c90-badb-2029e48e0699
-- title:
--   Orbit Tail Estimates: integrable long
-- statement:
--   The Orbit Tail Estimates construction uses the integrable long property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L265-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L265-L276

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

theorem Formalism.FourierDecayAlt.P.OrbitTailEstimates.integrable_long (m : ℕ) (β : ℂ) (r : ℝ) (hr : 0 < r) :
    Integrable (fun v : UT (m + 1 + 1) → ℂ => (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)))
      (muPi β (UT (m + 1 + 1))) := by sorry
