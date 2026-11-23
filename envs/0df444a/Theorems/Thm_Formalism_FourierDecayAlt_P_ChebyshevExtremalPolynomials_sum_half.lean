-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_sum_half
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.sum_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:35.966279+00:00
-- url     : https://prove2.me/theorems/c05a1860-29dd-4342-94eb-5869a0a2e760
-- title:
--   Chebyshev Extremal Polynomials: sum half
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the sum half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L154-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L154-L166

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.sum_half (m : ℕ) :
    ∑ j : Fin (m + 2), (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = (m:ℝ) + 1 := by sorry
