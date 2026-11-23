-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_coord_le
-- name    : Formalism.FourierDecayAlt.P.G7.norm_coord_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:00.818142+00:00
-- url     : https://prove2.me/theorems/2146c3b9-b623-4e6c-8d2f-d8612b46be77
-- title:
--   G7: norm coord le
-- statement:
--   The G7 construction uses the norm coord le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L489-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L489-L506

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

theorem Formalism.FourierDecayAlt.P.G7.norm_coord_le {n : ℕ} (t σ : ℂ) (x : UT n → ℂ) (B ρ : Fin n → ℂ) (Z : Mat (n + 1))
    (hZ : Z = Mcoord t (strictUpper x) B ρ σ) : ‖((ρ, x, B) : BlockCoord n)‖ ≤ ‖Z‖ := by sorry
