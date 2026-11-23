-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_lagCo_nd
-- name    : Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.lagCo_nd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:47.538144+00:00
-- url     : https://prove2.me/theorems/5014a8b2-e169-4e86-ba62-086811467b74
-- title:
--   Chebyshev Extremal Polynomials: lag Co nd
-- statement:
--   The Chebyshev Extremal Polynomials construction uses the lag Co nd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L123-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L123-L140

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

theorem Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.lagCo_nd (m : ℕ) (j : Fin (m + 2)) :
    lagCo (nd (m + 1)) j =
      (-1) ^ (j:ℕ) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 1 / 2 else 1) * ((2:ℝ) ^ m / ((m:ℝ) + 1)) := by sorry
