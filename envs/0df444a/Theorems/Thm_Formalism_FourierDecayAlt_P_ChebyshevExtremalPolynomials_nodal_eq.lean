-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_nodal_eq
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.nodal_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:40.766812+00:00
-- url     : https://prove2.me/theorems/92f34ad9-a379-43ee-9697-951b223986f9
-- title:
--   Chebyshev Extremal Polynomials: nodal eq
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the nodal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L39-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L39-L69

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

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.nodal_eq (m : ℕ) :
    (X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ) = C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1)) := by sorry
