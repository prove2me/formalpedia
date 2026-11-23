-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_gr_block_split
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_block_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:56.506998+00:00
-- url     : https://prove2.me/theorems/08585b87-d503-4516-ae7a-c1b430ea355b
-- title:
--   Diagonal Point Sigma Finite: gr block split
-- statement:
--   The Diagonal Point Sigma Finite construction uses the gr block split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L669-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L669-L675

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_block_split (β : ℂ) (n : ℕ) (τ : ℝ) (Φ : Mat (n + 1) → V) (t c : ℂ) (p : BlockCoord n) :
    blockIntegrand β n Φ t c p =
      blockIntegrand β n (cutPhi τ Φ) t c p + blockIntegrand β n (cutPhiC τ Φ) t c p := by sorry
