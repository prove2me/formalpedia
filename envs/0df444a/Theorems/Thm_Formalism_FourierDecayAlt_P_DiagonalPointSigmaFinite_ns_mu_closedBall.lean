-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_mu_closedBall
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_mu_closedBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:43.696735+00:00
-- url     : https://prove2.me/theorems/aebe496d-c1bd-4569-8778-c48bcf368d5b
-- title:
--   Diagonal Point Sigma Finite: ns mu closed Ball
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns mu closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L156-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L156-L166

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_mu_closedBall (β : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    mu β (Metric.closedBall 0 R) = ENNReal.ofReal (‖β‖ / 2 * R ^ 2) := by sorry
