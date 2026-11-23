-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_gr_osc_split
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_osc_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:59.611357+00:00
-- url     : https://prove2.me/theorems/ea0f380f-9326-4e94-90ae-7134c376cd20
-- title:
--   Diagonal Point Sigma Finite: gr osc split
-- statement:
--   The Diagonal Point Sigma Finite construction uses the gr osc split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L677-L683
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L677-L683

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_osc_split (β : ℂ) (m : ℕ) (δ ε : ℝ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) :
    oscIn β m ε Φ D t p = ((farCut m δ D p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p +
      ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p := by sorry
