-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_Fs_subset_ball
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_Fs_subset_ball
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:17.205067+00:00
-- url     : https://prove2.me/theorems/a08c8cf0-8767-4ad5-9e34-d346f58856e4
-- title:
--   Diagonal Point Sigma Finite: ns Fs subset ball
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns Fs subset ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L202-L206

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_Fs_subset_ball (m : ℕ) (D' : ℂ) (R r d : ℝ) (hR : 0 ≤ R) :
    ns_Fs m D' R r d ⊆ Metric.closedBall 0 R := by sorry
