-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_singleton_subset_detSet
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.singleton_subset_detSet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:55.891676+00:00
-- url     : https://prove2.me/theorems/77aa394b-a6e0-4fd8-9156-0c543b660b2f
-- title:
--   Diagonal Point Sigma Finite: singleton subset det Set
-- statement:
--   The Diagonal Point Sigma Finite construction uses the singleton subset det Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L56-L60

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.singleton_subset_detSet {m : ℕ} {Kc : Set ℂ} {D : ℂ} (hD : D ∈ Kc) :
    ({(wMat (m + 1)).det * D} : Set ℂ) ⊆ detSet (m + 1) Kc := by sorry
