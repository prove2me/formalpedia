-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_VandermondePolynomialIntegral_poly_integral
-- name    : Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.poly_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:17.580724+00:00
-- url     : https://prove2.me/theorems/caf7870f-eeeb-4ce7-8d43-76d2ed5b3718
-- title:
--   Vandermonde Polynomial Integral: poly integral
-- statement:
--   The Vandermonde Polynomial Integral construction uses the poly integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoeffOfValues.lean#L38-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoeffOfValues.lean#L38-L77

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoeffOfValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.poly_integral (μ : Measure X) (d : ℕ) (I : ℝ → X → E) (T : X → E) (hI : ∀ y, Integrable (I y) μ)
    (hP : ∀ᵐ x ∂μ, ∃ c : Fin (d + 1) → E, c (Fin.last d) = T x ∧ ∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n) :
    ∃ c : Fin (d + 1) → E, c (Fin.last d) = ∫ x, T x ∂μ ∧
      ∀ y : ℝ, ∫ x, I y x ∂μ = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by sorry
