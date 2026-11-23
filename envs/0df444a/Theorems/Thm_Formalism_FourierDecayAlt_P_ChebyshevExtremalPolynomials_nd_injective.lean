-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_nd_injective
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.nd_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:56.847154+00:00
-- url     : https://prove2.me/theorems/6a85b6b1-d64c-4fb8-9130-603ca3db77f5
-- title:
--   Chebyshev Extremal Polynomials: nd injective
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the nd injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L24-L28

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

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.nd_injective (n : ℕ) : Function.Injective (nd n) := by sorry
