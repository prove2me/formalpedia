-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_U_mul_sin_node
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.U_mul_sin_node
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:36.468803+00:00
-- url     : https://prove2.me/theorems/b1312180-3985-47ec-a37c-ae1b7440d3ec
-- title:
--   Chebyshev Extremal Polynomials: U mul sin node
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the U mul sin node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L30-L37

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

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.U_mul_sin_node (m : ℕ) (j : ℕ) :
    (Chebyshev.U ℝ (m:ℤ)).eval (Chebyshev.node (m + 1) j) * Real.sin (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = 0 := by sorry
