-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_mem_rootSet
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_mem_rootSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:45.487719+00:00
-- url     : https://prove2.me/theorems/e4cdac5a-dcf3-4a11-8a4f-c6b08f308274
-- title:
--   Diagonal Point Sigma Finite: ns mem root Set
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns mem root Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L175-L177

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_mem_rootSet {s : ℕ} (hs : 0 < s) (a z : ℂ) : z ∈ rootSet s a ↔ z ^ s = a := by sorry
