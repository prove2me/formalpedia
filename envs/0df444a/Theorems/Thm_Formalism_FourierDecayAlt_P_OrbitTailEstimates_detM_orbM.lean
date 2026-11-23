-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_detM_orbM
-- name    : Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:26.722805+00:00
-- url     : https://prove2.me/theorems/1a0bee84-8bf7-45ab-82d4-109b5318225c
-- title:
--   Orbit Tail Estimates: det M orb M
-- statement:
--   The Orbit Tail Estimates construction uses the det M orb M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L104-L105

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

theorem Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM (n : ℕ) (t c : ℂ) (p : BlockCoord n) :
    detM (orbM n t c p) = (wMat n).det * (c * t ^ n) := by sorry
