-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_one_le_tau
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.one_le_tau
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:58.776769+00:00
-- url     : https://prove2.me/theorems/a41df740-d2cd-4064-9e19-e80ccab663b2
-- title:
--   Diagonal Point Sigma Finite: one le tau
-- statement:
--   The Diagonal Point Sigma Finite construction uses the one le tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L62-L63

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.one_le_tau {t : ℂ} {ε : ℝ} (ht : t ≠ 0) (ht1 : ‖t‖ ≤ 1) (hε : 0 ≤ ε) : 1 ≤ ‖t‖ ^ (-ε) := by sorry
