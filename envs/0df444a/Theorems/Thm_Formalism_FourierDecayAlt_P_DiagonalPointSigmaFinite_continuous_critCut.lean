-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_continuous_critCut
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.continuous_critCut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:29.840833+00:00
-- url     : https://prove2.me/theorems/cc4bfa60-2b33-4739-a1ca-ea100ad6c795
-- title:
--   Diagonal Point Sigma Finite: continuous crit Cut
-- statement:
--   The Diagonal Point Sigma Finite construction uses the continuous crit Cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L69-L71

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.continuous_critCut {n : ℕ} (δ : ℝ) (z : ℂ) : Continuous (critCut (n := n) δ z) := by sorry
