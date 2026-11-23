-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_powMulVec
-- name    : Formalism.FourierDecayAlt.P.G7.continuous_powMulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:45.421373+00:00
-- url     : https://prove2.me/theorems/99fd6112-7053-4bf0-a2e6-5c0faa46d81d
-- title:
--   G7: continuous pow Mul Vec
-- statement:
--   The G7 construction uses the continuous pow Mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L297-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L297-L299

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

theorem Formalism.FourierDecayAlt.P.G7.continuous_powMulVec (m j : ℕ) : Continuous
    (fun z : (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) => (-(strictUpper z.1)) ^ j *ᵥ z.2) := by sorry
