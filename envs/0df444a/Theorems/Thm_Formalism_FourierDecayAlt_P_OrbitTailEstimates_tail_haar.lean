-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_tail_haar
-- name    : Formalism.FourierDecayAlt.P.OrbitTailEstimates.tail_haar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:11.632665+00:00
-- url     : https://prove2.me/theorems/f63e70fb-938f-4f35-adda-73a79ad4653c
-- title:
--   Orbit Tail Estimates: tail haar
-- statement:
--   The Orbit Tail Estimates construction uses the tail haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L47-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L47-L68

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem Formalism.FourierDecayAlt.P.OrbitTailEstimates.tail_haar (ν : Measure E) [ν.IsAddHaarMeasure] (T A : ℝ) (hT : 1 ≤ T)
    (hA : (Module.finrank ℝ E : ℝ) + 1 ≤ A) :
    Integrable (fun q : E => (max T ‖q‖) ^ (-A)) ν ∧
    ∫ q : E, (max T ‖q‖) ^ (-A) ∂ν ≤
      T ^ ((Module.finrank ℝ E : ℝ) - A) * ∫ q : E, (max 1 ‖q‖) ^ (-((Module.finrank ℝ E : ℝ) + 1)) ∂ν := by sorry
