-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_isClosed_Fs
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_isClosed_Fs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:47.834791+00:00
-- url     : https://prove2.me/theorems/a9d1b2cf-26d2-4f0a-9138-a217144ac8c2
-- title:
--   Diagonal Point Sigma Finite: ns is Closed Fs
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns is Closed Fs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L193-L200

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_isClosed_Fs (m : ℕ) (D' : ℂ) (R r d : ℝ) : IsClosed (ns_Fs m D' R r d) := by sorry
