-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_norm_blockIntegrand
-- name    : Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_blockIntegrand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:01.106704+00:00
-- url     : https://prove2.me/theorems/41507ea9-b727-47c7-888f-6e7cadf5d8fd
-- title:
--   Orbit Tail Estimates: norm block Integrand
-- statement:
--   The Orbit Tail Estimates construction uses the norm block Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L107-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L107-L111

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

theorem Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_blockIntegrand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (n : ℕ)
    (Φ : Mat (n + 1) → V) (t c : ℂ) (p : BlockCoord n) :
    ‖blockIntegrand β n Φ t c p‖ = ‖Φ (orbM n t c p)‖ := by sorry
