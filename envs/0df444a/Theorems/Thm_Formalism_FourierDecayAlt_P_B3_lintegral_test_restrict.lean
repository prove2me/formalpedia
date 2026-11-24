-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_lintegral_test_restrict
-- name    : Formalism.FourierDecayAlt.P.B3.lintegral_test_restrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:24.96306+00:00
-- url     : https://prove2.me/theorems/f777ced2-f06f-4e2d-b19c-7fdfca91376b
-- title:
--   B3: lintegral test restrict
-- statement:
--   The B3 construction uses the lintegral test restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L218-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L218-L227

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

theorem Formalism.FourierDecayAlt.P.B3.lintegral_test_restrict {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ τ : ℝ × ℝ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * F τ) =
      ∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * F τ ∂(volume.restrict Quad) := by sorry
