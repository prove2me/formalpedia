-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_ae_eq_of_tests
-- name    : Formalism.FourierDecayAlt.P.B3.ae_eq_of_tests
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:30:14.117611+00:00
-- url     : https://prove2.me/theorems/e49658ff-5af9-455b-b6e6-36518a905de0
-- title:
--   B3: ae eq of tests
-- statement:
--   The B3 construction uses the ae eq of tests property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L157-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L157-L216

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

theorem Formalism.FourierDecayAlt.P.B3.ae_eq_of_tests {f g : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict Quad))
    (hg : AEMeasurable g (volume.restrict Quad)) (hfin : FinT f)
    (H : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * f τ ∂(volume.restrict Quad)) =
        ∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * g τ ∂(volume.restrict Quad)) :
    f =ᵐ[volume.restrict Quad] g := by sorry
