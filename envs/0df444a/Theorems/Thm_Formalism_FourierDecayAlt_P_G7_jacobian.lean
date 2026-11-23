-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_jacobian
-- name    : Formalism.FourierDecayAlt.P.G7.jacobian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:45.399507+00:00
-- url     : https://prove2.me/theorems/0058d867-3454-4a8a-8d5a-74547aac4300
-- title:
--   G7: jacobian
-- statement:
--   The G7 construction uses the jacobian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L99-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L99-L105

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

theorem Formalism.FourierDecayAlt.P.G7.jacobian (n : ℕ) (β t : ℂ) (ht : t ≠ 0) :
    Measure.map (coordMap n t) (muBlock β n) = Real.toNNReal ((‖t‖ ^ (n * (n + 3)))⁻¹) • muBlock β n := by sorry
