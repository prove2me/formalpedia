-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_critCut_mem_Icc
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.critCut_mem_Icc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:28.051803+00:00
-- url     : https://prove2.me/theorems/c0c8c9da-4fd2-4991-a255-cb223256f171
-- title:
--   Diagonal Point Sigma Finite: crit Cut mem Icc
-- statement:
--   The Diagonal Point Sigma Finite construction uses the crit Cut mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L80-L82

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.critCut_mem_Icc {n : ℕ} (δ : ℝ) (z : ℂ) (x : Fin n → ℂ) : 0 ≤ critCut δ z x ∧ critCut δ z x ≤ 1 := by sorry
