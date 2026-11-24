-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_integral_test_parts
-- name    : Formalism.FourierDecayAlt.P.B3.integral_test_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:06.996412+00:00
-- url     : https://prove2.me/theorems/efb4c261-3a09-4ab8-9e8f-cf533570a41d
-- title:
--   B3: integral test parts
-- statement:
--   The B3 construction uses the integral test parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L261-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L261-L270

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B

theorem Formalism.FourierDecayAlt.P.B3.integral_test_parts {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂)
    {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) :
    (∫ τ, w₁ τ.1 * w₂ τ.2 * h τ ∂(volume.restrict Quad)) =
      (∫ τ, w₁ τ.1 * w₂ τ.2 * max (h τ) 0 ∂(volume.restrict Quad)) -
        ∫ τ, w₁ τ.1 * w₂ τ.2 * max (-h τ) 0 ∂(volume.restrict Quad) := by sorry
