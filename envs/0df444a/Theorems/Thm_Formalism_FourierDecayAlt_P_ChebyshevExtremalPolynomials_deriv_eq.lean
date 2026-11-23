-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_deriv_eq
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.deriv_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:27.079279+00:00
-- url     : https://prove2.me/theorems/25a43e3a-1d2e-4a3e-a412-b723c717b70e
-- title:
--   Chebyshev Extremal Polynomials: deriv eq
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the deriv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L71-L78

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

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.deriv_eq (m : ℕ) :
    derivative ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)) =
      ((m:ℝ[X]) + 1) * Chebyshev.T ℝ ((m:ℤ) + 1) + X * Chebyshev.U ℝ (m:ℤ) := by sorry
