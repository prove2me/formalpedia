-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_Fs_subset_Om
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_Fs_subset_Om
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:19.236724+00:00
-- url     : https://prove2.me/theorems/95408cfe-d8c8-4d14-9011-3cecac217ff0
-- title:
--   Diagonal Point Sigma Finite: ns Fs subset Om
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns Fs subset Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L208-L211

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_Fs_subset_Om (m : ℕ) (D' : ℂ) {R r r' d d' : ℝ} (hr : r' < r) (hd : d' < d) :
    ns_Fs m D' R r d ⊆ ns_Om m D' r' d' := by sorry
