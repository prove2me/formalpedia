-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_root_bound
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.root_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:54.829965+00:00
-- url     : https://prove2.me/theorems/5de3aa5d-cc2c-41ce-b759-36ed79ee24e0
-- title:
--   Diagonal Point Sigma Finite: root bound
-- statement:
--   The Diagonal Point Sigma Finite construction uses the root bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L106-L115

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.root_bound {m : ℕ} {Kc : Set ℂ} (hK : IsCompact Kc) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ D ∈ Kc, ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * D → ‖z‖ ≤ R := by sorry
