-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_detM_longM
-- name    : Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:43.118803+00:00
-- url     : https://prove2.me/theorems/3eb6f702-74d6-4527-b4ca-c8499e7caae6
-- title:
--   Orbit Tail Estimates: det M long M
-- statement:
--   The Orbit Tail Estimates construction uses the det M long M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L256-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L256-L263

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

theorem Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM (m : ℕ) (z D : ℂ) (hz : z ^ (m + 2) = (-1) ^ (m + 3) * D) (v : UT (m + 1 + 1) → ℂ) :
    detM (longM (m + 1 + 1) z v) = (wMat (m + 1)).det * D := by sorry
