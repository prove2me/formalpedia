-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_smooth_cutoff_mem_unit_interval
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.smooth_cutoff_mem_unit_interval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:48.277684+00:00
-- url     : https://prove2.me/theorems/c54ed039-1b2d-4bb7-93e7-6e91ae5719a6
-- title:
--   Diagonal Point Sigma Finite: smooth cutoff mem unit interval
-- statement:
--   The Diagonal Point Sigma Finite construction uses the smooth cutoff mem unit interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L77-L78

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.smooth_cutoff_mem_unit_interval (r : ℝ) : 0 ≤ chi0 r ∧ chi0 r ≤ 1 := by sorry
