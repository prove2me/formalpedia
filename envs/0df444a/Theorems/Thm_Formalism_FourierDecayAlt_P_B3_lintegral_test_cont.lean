-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_lintegral_test_cont
-- name    : Formalism.FourierDecayAlt.P.B3.lintegral_test_cont
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:18.005254+00:00
-- url     : https://prove2.me/theorems/58b37abb-d8b8-4fb8-887d-1e8e5556b50a
-- title:
--   B3: lintegral test cont
-- statement:
--   The B3 construction uses the lintegral test cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L244-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L244-L251

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

theorem Formalism.FourierDecayAlt.P.B3.lintegral_test_cont {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (p₁ : ∀ x, 0 ≤ w₁ x) (p₂ : ∀ x, 0 ≤ w₂ x)
    {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) (h0 : ∀ τ, 0 ≤ h τ) :
    (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * ENNReal.ofReal (h τ) ∂(volume.restrict Quad)) =
      ENNReal.ofReal (∫ τ, w₁ τ.1 * w₂ τ.2 * h τ ∂(volume.restrict Quad)) := by sorry
