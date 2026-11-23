-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_pointwise_red
-- name    : Formalism.FourierDecayAlt.P.G7.pointwise_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:14.235864+00:00
-- url     : https://prove2.me/theorems/2d4adf12-95e6-4a88-813d-9e35a7f75d6e
-- title:
--   G7: pointwise red
-- statement:
--   The G7 construction uses the pointwise red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L355-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L355-L382

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

theorem Formalism.FourierDecayAlt.P.G7.pointwise_red {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : Mat (m + 1 + 1) → V) (t c : ℂ) (ht : t ≠ 0) (q : RedCoord m) :
    ((‖t ^ (m + 1) / Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2 : ℝ) : ℂ) •
      Fint β m Φ t c (consMap m
        (t ^ (m + 1) / Cof (strictUpper q.2.2.1) q.2.2.2 t * q.1 +
          (-(c * t ^ (m + 1)) - R0 (strictUpper q.2.2.1) q.2.2.2 q.2.1 t) / Cof (strictUpper q.2.2.1) q.2.2.2 t,
          q.2)) =
    ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) •
      ((psi β ((rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t +
                ∑ k, xOf (strictUpper q.2.2.1) q.2.2.2 k) / t) *
              (((‖Cof (strictUpper q.2.2.1) q.2.2.2 t‖ ^ 2)⁻¹ : ℝ) : ℂ)) •
            Φ (Mcoord t (strictUpper q.2.2.1) q.2.2.2
              (Fin.cons (rho1 (c * t ^ (m + 1)) q.1 q.2.1 (strictUpper q.2.2.1) q.2.2.2 t) q.2.1) q.1)) := by sorry
