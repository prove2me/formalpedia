-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_differentiableOn
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_differentiableOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:47.818373+00:00
-- url     : https://prove2.me/theorems/f1562fa6-b0a1-40bc-9d06-347fcbb9cbc4
-- title:
--   Diagonal Point Sigma Finite: ns differentiable On
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L213-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L213-L225

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_differentiableOn (m : ℕ) (D' : ℂ) {r d : ℝ} (hr : 0 ≤ r) :
    DifferentiableOn ℂ (g0 D') (ns_Om m D' r d) := by sorry
