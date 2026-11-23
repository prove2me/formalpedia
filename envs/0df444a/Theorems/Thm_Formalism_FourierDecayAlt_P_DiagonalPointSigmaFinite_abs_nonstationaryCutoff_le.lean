-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_abs_nonstationaryCutoff_le
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.abs_nonstationaryCutoff_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:53.365156+00:00
-- url     : https://prove2.me/theorems/318d1531-c331-4810-b4de-2e41c38ac9bb
-- title:
--   Diagonal Point Sigma Finite: abs nonstationary Cutoff le
-- statement:
--   The Diagonal Point Sigma Finite construction uses the abs nonstationary Cutoff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L94-L104

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.abs_nonstationaryCutoff_le (m : ℕ) (δ : ℝ) (D : ℂ) (x : Fin (m + 1) → ℂ) :
    |farCut m δ D x| ≤ 1 + ((rootSet (m + 2) ((-1) ^ (m + 3) * D)).card : ℝ) := by sorry
