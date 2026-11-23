-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_coeff_mono
-- name    : Formalism.FourierDecayAlt.P.TopDegreePolynomials.coeff_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:16.16422+00:00
-- url     : https://prove2.me/theorems/41ee1498-49a8-4d33-8c49-76006e075fa0
-- title:
--   Top Degree Polynomials: coeff mono
-- statement:
--   The Top Degree Polynomials construction uses the coeff mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L39-L48

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TopDegreePolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.TopDegreePolynomials.coeff_mono (h : ℂ) (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).coeff (a + b) = if i = a ∧ j = b then 1 else 0 := by sorry
