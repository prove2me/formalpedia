-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_derivBound_mono
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.derivBound_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:39.861387+00:00
-- url     : https://prove2.me/theorems/d65acf10-35f2-4a6f-8e3f-2e733d3d081f
-- title:
--   Diagonal Point Sigma Finite: deriv Bound mono
-- statement:
--   The Diagonal Point Sigma Finite construction uses the deriv Bound mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L21-L25

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.derivBound_mono {s : ℕ} {k k' : ℕ} {Kd Kd' : Set ℂ} {bd : Mat s → ℝ} {Φ : Mat s → V}
    (h : DerivBound k Kd bd Φ) (hk : k' ≤ k) (hK : Kd' ⊆ Kd) : DerivBound k' Kd' bd Φ := by sorry
