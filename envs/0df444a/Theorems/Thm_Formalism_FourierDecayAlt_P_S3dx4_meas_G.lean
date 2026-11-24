-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_meas_G
-- name    : Formalism.FourierDecayAlt.P.S3dx4.meas_G
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:04.701928+00:00
-- url     : https://prove2.me/theorems/36286c8f-0a6c-4bd8-aaf2-067e892692ab
-- title:
--   S3dx4: meas G
-- statement:
--   The S3dx4 construction uses the meas G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TripleIntegrandMeasurable.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TripleIntegrandMeasurable.lean#L16-L27

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.meas_G (γ : Mx k r) (b : ℝ) :
    Measurable (fun pp : B.SS k r =>
      ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ * (Matrix.of pp.2.1)⁻¹) ^ (-b)‖ₑ) := by sorry
