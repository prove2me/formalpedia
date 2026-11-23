-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_vpow
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_vpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:58.048974+00:00
-- url     : https://prove2.me/theorems/f4cf871e-07b3-4612-97cf-afb78210320c
-- title:
--   Diagonal Point Sigma Finite: ns vpow
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns vpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L227-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L227-L230

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_vpow {τ ε e : ℝ} (hτ : 0 ≤ τ) (n : ℕ) (hn : (n : ℝ) = e) :
    τ ^ (-(ε * e)) = (τ ^ (-ε)) ^ n := by sorry
