-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_VandermondePolynomialIntegral_coeff_of_values
-- name    : Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.coeff_of_values
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:18.665398+00:00
-- url     : https://prove2.me/theorems/a902bc24-6d92-5e53-b246-657d3e2baf2a
-- title:
--   Vandermonde Polynomial Integral: coeff of values
-- statement:
--   The Vandermonde Polynomial Integral construction uses the coeff of values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoeffOfValues.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoeffOfValues.lean#L21-L32

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
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.coeff_of_values (d : ℕ) (c : Fin (d + 1) → E) (n : Fin (d + 1)) :
    ∑ m, (vN d)⁻¹ n m • ∑ n' : Fin (d + 1), ((((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' = c n := by sorry
