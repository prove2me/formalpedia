-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_norm_omLong_le
-- name    : Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_omLong_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:16.874034+00:00
-- url     : https://prove2.me/theorems/c3df2dd2-b352-48a1-89d5-d51cb27a3213
-- title:
--   Orbit Tail Estimates: norm om Long le
-- statement:
--   The Orbit Tail Estimates construction uses the norm om Long le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L278-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L278-L298

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

theorem Formalism.FourierDecayAlt.P.OrbitTailEstimates.norm_omLong_le (m : ℕ) (β : ℂ) (r : ℝ) (hr : 0 < r) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : Mat (m + 1 + 1) → V) (A K : ℝ) (hA : ((m : ℝ) + 1) * ((m : ℝ) + 4) + 1 ≤ A) (hK : 0 ≤ K) (z : ℂ)
    (hz : r ≤ ‖z‖)
    (hb : ∀ v, ‖Φ (longM (m + 1 + 1) z v)‖ ≤ K * min 1 (‖longM (m + 1 + 1) z v‖ ^ (-A))) :
    ‖OmLong β (m + 1) Φ z‖ ≤ K * ∫ v : UT (m + 1 + 1) → ℂ,
      (max 1 ‖r • v‖) ^ (-(((m : ℝ) + 1) * ((m : ℝ) + 4) + 1)) ∂(muPi β (UT (m + 1 + 1))) := by sorry
