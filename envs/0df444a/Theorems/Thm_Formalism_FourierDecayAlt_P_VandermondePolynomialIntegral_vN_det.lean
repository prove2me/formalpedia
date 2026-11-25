-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_VandermondePolynomialIntegral_vN_det
-- name    : Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.vN_det
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:34.413954+00:00
-- url     : https://prove2.me/theorems/fb3715fd-bfbc-4cbd-82be-bd307e9c1406
-- title:
--   Vandermonde Polynomial Integral: v N det
-- statement:
--   The Vandermonde Polynomial Integral construction uses the v N det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoeffOfValues.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoeffOfValues.lean#L15-L19

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

theorem Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.vN_det (d : ℕ) : IsUnit (vN d).det := by sorry
