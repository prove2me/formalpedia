-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_root_ne_zero
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.root_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:53.416473+00:00
-- url     : https://prove2.me/theorems/ed1a8d7b-7320-4c39-b54d-f9553d2ce468
-- title:
--   Diagonal Point Sigma Finite: root ne zero
-- statement:
--   The Diagonal Point Sigma Finite construction uses the root ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L117-L125

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.root_ne_zero {m : ℕ} {Kc : Set ℂ} (h0 : (0 : ℂ) ∉ Kc) {D : ℂ} (hD : D ∈ Kc) {z : ℂ}
    (hz : z ^ (m + 2) = (-1) ^ (m + 3) * D) : z ≠ 0 := by sorry
