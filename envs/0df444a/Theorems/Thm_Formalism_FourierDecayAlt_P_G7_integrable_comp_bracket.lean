-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_integrable_comp_bracket
-- name    : Formalism.FourierDecayAlt.P.G7.integrable_comp_bracket
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:00:19.062991+00:00
-- url     : https://prove2.me/theorems/352e11c4-2733-4d14-98aa-eec4e43b5a43
-- title:
--   G7: integrable comp bracket
-- statement:
--   The G7 construction uses the integrable comp bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L444-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L444-L451

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

theorem Formalism.FourierDecayAlt.P.G7.integrable_comp_bracket {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν μ : Measure E) [ν.IsAddHaarMeasure] (k κ : NNReal)
    (hμ : μ = k • ν) (f : E → E) (hf : MeasurableEmbedding f) (hmap : Measure.map f μ = κ • μ) (A : ℝ)
    (hA : (Module.finrank ℝ E : ℝ) < A) : Integrable (fun p => (1 + ‖f p‖) ^ (-A)) μ := by sorry
