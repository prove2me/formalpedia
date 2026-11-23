-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_ns_isOpen_Om
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_isOpen_Om
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:58.145809+00:00
-- url     : https://prove2.me/theorems/dcd5d42f-30e7-4956-a1f0-4c4d710d1966
-- title:
--   Diagonal Point Sigma Finite: ns is Open Om
-- statement:
--   The Diagonal Point Sigma Finite construction uses the ns is Open Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L182-L188

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_isOpen_Om (m : ℕ) (D' : ℂ) (r d : ℝ) : IsOpen (ns_Om m D' r d) := by sorry
